# Higher-Order Abstract Syntax in Lean

A literate introduction to higher-order abstract syntax (HOAS), written in
[Verso](https://github.com/leanprover/verso). Text and Lean are mixed in the
same files, and every `lean` block is elaborated. Everything is built from
scratch: there are no HOAS libraries, and no Mathlib.

Pinned to Lean **4.34.0** and Verso **v4.34.0**.

## Where to start

Open `LeanHoas.lean`. It is the book root: a short motivation, then the
chapters in reading order.

| Chapter | File | Point |
| --- | --- | --- |
| Binders, the Hard Way | `LeanHoas/Named.lean` | Named syntax: capture, α-equivalence |
| Nameless, but Not Effortless | `LeanHoas/DeBruijn.lean` | Indices trade names for shifting |
| Let the Host Bind | `LeanHoas/Naive.lean` | Naive HOAS: rejected, then exotic |
| Parametric HOAS | `LeanHoas/PHOAS/Basic.lean` | One term, many interpretations |
| Substitution Is Instantiation | `LeanHoas/PHOAS/Subst.lean` | Substitution without traversal |
| The Small Print: Parametricity | `LeanHoas/PHOAS/Exotic.lean` | Exotic terms in Lean, and `Wf` |
| Typed HOAS | `LeanHoas/Typed/Basic.lean` | Environment-free interpreter |
| A Verified Transformation | `LeanHoas/Typed/ConstFold.lean` | Constant folding, proved correct |

Each chapter imports only the chapters it builds on, so go-to-definition
works across chapters.

## Build

The first build compiles Verso from source, which takes several minutes. The
artifact cache is enabled (`enableArtifactCache`), so other projects pinned
to the same Verso reuse it.

```sh
export LEAN_NUM_THREADS=2
nice -n 15 lake env lake build
nice -n 15 lake env lake exe lean-hoas
python3.11 -m http.server 8000 -d _out/html-multi
```

Then open <http://localhost:8000/>. `lake env` is required so that child
processes see `LD_LIBRARY_PATH`.

## Publishing

`.github/workflows/pages.yml` builds the book on every push and pull
request, and deploys `_out/html-multi` with GitHub Pages from `main`.

## Source conventions

- Named `lean` blocks pair with `leanOutput` blocks. The output is checked at
  build time.
- `+error` blocks must fail. Add `-keep` so a rejected declaration leaves
  nothing in the environment.
- `-show` blocks are plumbing: elaborated, but hidden from the rendered
  text.
- The HTML executable imports every chapter, and closed top-level terms
  are evaluated when a module is initialized. A diverging `unsafe`
  definition must therefore be `noncomputable`, or the executable
  overflows its stack at startup.
