// Host side of the embedding ABI a `cantor build --target wasm32` module
// exposes — see cantor-runtime/src/wasm.rs for the other half.
//
// The compiled program is an event loop that can't block on input, so the
// page owns the loop and calls one Event in at a time. Strings cross as
// UTF-8 bytes in the module's linear memory. Output crosses back either as
// text (CantorProgram, the original Char* shape) or as a bitmap
// (CantorImageProgram, the Image convention — docs/design-decisions.md §6)
// — which one a given module supports is fixed at `cantor build` time
// (`wasm_driver_source`'s exports differ per Output shape), so use whichever
// class matches the module you compiled, not both against the same module.
//
// `showProgramSource` at the bottom is the one thing here that isn't ABI —
// shared page furniture, kept alongside it so both demos agree.

async function instantiate(url) {
  try {
    return await WebAssembly.instantiateStreaming(fetch(url), {});
  } catch {
    // instantiateStreaming rejects if the server sends the wrong
    // Content-Type, which is easy to hit when previewing through a minimal
    // static server. Buffering the whole module works regardless.
    const bytes = await (await fetch(url)).arrayBuffer();
    return await WebAssembly.instantiate(bytes, {});
  }
}

export class CantorProgram {
  #exports;

  constructor(exports) {
    this.#exports = exports;
    exports.cantor_wasm_init();
  }

  static async load(url) {
    const result = await instantiate(url);
    return new CantorProgram(result.instance.exports);
  }

  // A fresh view every time: the module's memory can grow during a step,
  // which detaches any ArrayBuffer view taken before the call.
  get #memory() {
    return new Uint8Array(this.#exports.memory.buffer);
  }

  // Feed one Event through the program and return its Output.
  step(event) {
    const bytes = new TextEncoder().encode(event);
    const ptr = this.#exports.cantor_wasm_input_buffer(bytes.length);
    this.#memory.set(bytes, ptr);

    this.#exports.cantor_wasm_step(bytes.length);

    const outPtr = this.#exports.cantor_wasm_output_ptr();
    const outLen = this.#exports.cantor_wasm_output_len();
    return new TextDecoder().decode(this.#memory.slice(outPtr, outPtr + outLen));
  }
}

// The Image-Output counterpart of `CantorProgram` — same Event-in/step
// protocol, but Output is a bitmap (`Nat * Nat * Unsigned32*`, packed RGBA
// pixels) instead of text. `step` returns an `ImageData`, ready for
// `ctx.putImageData(imageData, 0, 0)`.
export class CantorImageProgram {
  #exports;

  constructor(exports) {
    this.#exports = exports;
    exports.cantor_wasm_init();
  }

  static async load(url) {
    const result = await instantiate(url);
    return new CantorImageProgram(result.instance.exports);
  }

  get #memory() {
    return new Uint8Array(this.#exports.memory.buffer);
  }

  // Feed one Event through the program and return its Output as an
  // `ImageData`.
  step(event) {
    const bytes = new TextEncoder().encode(event);
    const ptr = this.#exports.cantor_wasm_input_buffer(bytes.length);
    this.#memory.set(bytes, ptr);

    this.#exports.cantor_wasm_step(bytes.length);

    const width = this.#exports.cantor_wasm_output_width();
    const height = this.#exports.cantor_wasm_output_height();
    const pixelsPtr = this.#exports.cantor_wasm_output_pixels_ptr();
    const pixelsLen = this.#exports.cantor_wasm_output_pixels_len();

    // Copy out of wasm memory into ImageData's own backing store: its
    // pixels are already row-major RGBA, exactly what ImageData wants, but
    // holding a view over the module's memory past this call would be
    // unsafe — the module's memory can grow (detaching this view) before
    // the next step.
    const pixels = new Uint8ClampedArray(pixelsLen);
    pixels.set(this.#memory.subarray(pixelsPtr, pixelsPtr + pixelsLen));
    return new ImageData(pixels, width, height);
  }
}

// Demo-page support rather than part of the embedding ABI: show the .cantor
// source a module was built from, fetched at page load instead of pasted into
// the HTML. The demo pages used to inline a copy, which silently went stale
// the first time the example changed; `web/*.cantor` are symlinks to the real
// `examples/*.cantor`, so what a reader sees is always what was compiled.
export async function showProgramSource(element, url) {
  try {
    const response = await fetch(url);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    element.textContent = await response.text();
  } catch (e) {
    // Worth surfacing rather than leaving "Loading…" on screen: the usual
    // cause is serving the page without the sources alongside it, and the
    // link above the block still gets the reader to the program.
    element.textContent = `could not load ${url}: ${e.message}`;
    element.classList.add("error");
  }
}

// The end-of-input Event a Cantor program sees when its input stream closes
// (ASCII EOT) — docs/design-decisions.md §6.
export const EOT_EVENT = "\u0004";
