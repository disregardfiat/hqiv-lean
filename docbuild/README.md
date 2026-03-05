# Building HQIV_LEAN documentation

This directory is the [doc-gen4](https://github.com/leanprover/doc-gen4) build for the main package.

## First-time setup

From this directory (`docbuild/`):

```bash
# If the parent project depends on mathlib (recommended):
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4

# Update the parent dependency when you change the main lakefile or deps:
lake update hqiv-lean
```

## Build the docs

From this directory:

```bash
lake build HQIVLEAN:docs
```

Output is under `docbuild/.lake/build/doc/`. Open `docbuild/.lake/build/doc/index.html` in a browser. For correct linking you should serve the directory over HTTP, e.g.:

```bash
cd .lake/build/doc && python3 -m http.server 8000
```

Then open http://localhost:8000 .

## From the repo root

You can also run:

```bash
cd docbuild && lake build HQIVLEAN:docs
```
