// Host side of the embedding ABI a `cantor build --target wasm32` module
// exposes — see cantor-runtime/src/wasm.rs for the other half.
//
// The compiled program is an event loop that can't block on input, so the
// page owns the loop and calls one Event in at a time. Strings cross as
// UTF-8 bytes in the module's linear memory.

export class CantorProgram {
  #exports;

  constructor(exports) {
    this.#exports = exports;
    exports.cantor_wasm_init();
  }

  static async load(url) {
    let result;
    try {
      result = await WebAssembly.instantiateStreaming(fetch(url), {});
    } catch {
      // instantiateStreaming rejects if the server sends the wrong
      // Content-Type, which is easy to hit when previewing through a
      // minimal static server. Buffering the whole module works regardless.
      const bytes = await (await fetch(url)).arrayBuffer();
      result = await WebAssembly.instantiate(bytes, {});
    }
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

// The end-of-input Event a Cantor program sees when its input stream closes
// (ASCII EOT) — docs/design-decisions.md §6.
export const EOT_EVENT = "\u0004";
