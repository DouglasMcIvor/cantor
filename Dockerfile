FROM rust:latest

# rustfmt/clippy aren't part of the `rust:latest` image's default component
# set — install them so `cargo fmt --check` / `cargo clippy` can run locally.
# CI's fmt/clippy steps are still commented out in .github/workflows/rust.yml
# (the repo isn't clean under them yet); this is the prerequisite for doing
# that cleanup.
RUN rustup component add rustfmt clippy

# Install Node.js and npm for Claude Code CLI
RUN curl -fsSL https://deb.nodesource.com/setup_20.x | bash - && \
    apt-get install -y nodejs && \
    rm -rf /var/lib/apt/lists/*

# Build dependencies for the cantor compiler itself (see README.md "Building"
# and .github/workflows/rust.yml, which install the same packages for CI).
# NOTE: libcvc5-dev is deliberately NOT installed from apt here. Debian's
# packaged version (1.1.2 on trixie, which `rust:latest` currently tracks) is
# API-incompatible with the cvc5 Rust crate this project pins (which requires
# cvc5 1.3.1 — see [package.metadata.cvc5] in the cvc5-sys crate, and
# Cargo.lock's `cvc5`/`cvc5-sys` entries): the 1.1.2 C API header has a
# `#include <cstdint>` bug that breaks bindgen, and even worked around, several
# functions are named differently between 1.1.2 and 1.3.1 (e.g.
# `cvc5_mk_dt_consdecl` vs `cvc5_mk_dt_cons_decl`), so the build fails either
# at the build-script stage or with "cannot find function" errors at compile
# time. Ubuntu 26.04 (used by CI) happens to package a matching 1.3.x version
# (1.3.2-1build1, built by Ubuntu from source), which is why
# `apt-get install libcvc5-dev` works there but not here. Instead, install
# the official prebuilt cvc5 1.3.1 release directly under /usr/local, and
# point the cvc5-sys build script (cvc5-sys/build.rs) at it via
# CVC5_LIB_DIR. That env var is required even though /usr/local/lib is on
# gcc's and GNU ld's default search paths: rustc links with its bundled
# rust-lld (see `-fuse-ld=lld` in the linker invocation), which — unlike
# GNU ld — does NOT search /usr/local/lib by default, and cvc5-sys only emits
# `cargo:rustc-link-search` when CVC5_LIB_DIR is set (it has no "static"
# feature enabled here, so it otherwise assumes the libs are already on the
# linker's default path). Bump the version/URL here in lockstep with any
# cvc5 crate upgrade.
#
# NOTE (2026-07-04): this prebuilt 1.3.1 binary segfaults under `cargo test`
# when cvc5 is called concurrently from multiple threads, even with
# independent TermManager/Solver instances per thread — src/solver/mod.rs
# now serializes all cvc5 calls behind a process-wide Mutex to guard against
# this. CI's Ubuntu-built 1.3.2 hasn't reproduced the crash across several
# parallel `cargo test` runs, so this may be specific to this prebuilt
# binary's version or build provenance rather than a cvc5-version-agnostic
# issue — not confirmed either way from upstream's changelog, so keep the
# Mutex regardless of which cvc5 build ends up in use.
RUN apt-get update && \
    apt-get install -y llvm-18-dev libclang-18-dev unzip && \
    rm -rf /var/lib/apt/lists/* && \
    curl -fsSL -o /tmp/cvc5.zip \
      https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-Linux-x86_64-shared.zip && \
    unzip -q /tmp/cvc5.zip -d /tmp/cvc5-extracted && \
    cp -r /tmp/cvc5-extracted/cvc5-Linux-x86_64-shared/include/. /usr/local/include/ && \
    cp -P /tmp/cvc5-extracted/cvc5-Linux-x86_64-shared/lib/*.so* /usr/local/lib/ && \
    ldconfig && \
    rm -rf /tmp/cvc5.zip /tmp/cvc5-extracted
ENV CVC5_LIB_DIR=/usr/local/lib

# Install Claude Code CLI
RUN npm install -g @anthropic-ai/claude-code

# Create a non-root user for running builds
# Matches the host user's name/uid/gid so bind-mounted dotfiles (which may
# contain absolute host-path symlinks, e.g. the Claude CLI's own install)
# resolve correctly inside the container too.
ARG HOST_USER=dev
ARG HOST_UID=1000
ARG HOST_GID=1000
RUN groupadd -g ${HOST_GID} ${HOST_USER} && \
    useradd -m -u ${HOST_UID} -g ${HOST_GID} -s /bin/bash ${HOST_USER}

# Set working directory
WORKDIR /project

# Switch to non-root user
USER ${HOST_USER}

# Set up shell
SHELL ["/bin/bash", "-c"]

# Default to bash
ENTRYPOINT ["/bin/bash"]
