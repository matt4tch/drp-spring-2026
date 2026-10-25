# Iteration of Linear Differential Operators

This repository contains a University of Waterloo Directed Research Program
project by Jake Edmonstone and Matthew Tchouikine, mentored by Paul Cusson.

The project begins with a question about repeatedly differentiating a smooth
function: if the sequence of derivatives

$$
f(x), f'(x), f''(x), \ldots
$$

converges pointwise, what can its limit be? The write-up proves that the limit
must satisfy \(g' = g\), so it has the form \(g(x) = Ce^x\). It then studies
analogous questions for first-order linear differential operators
\(L f = a f' + b f\), including examples where the leading coefficient
vanishes.

## Files

- [papers/smooth-iterates.typ](papers/smooth-iterates.typ) — the original
  mathematical write-up and proofs ([PDF](papers/smooth-iterates.pdf)).
- [papers/analytic-iterates.typ](papers/analytic-iterates.typ) — analytic
  differential-operator iterates and a singular counterexample
  ([PDF](papers/analytic-iterates.pdf)). Its bibliography is
  `papers/analytic-iterates.bib`.
- [presentation/slides.typ](presentation/slides.typ) — the presentation
  ([PDF](presentation/slides.pdf)), with its sections and assets in
  `presentation/sections/` and `presentation/assets/`.
- `styles/` — shared paper and presentation formatting.
- `lean/` — the Lean formalization of the original results; see its
  [README](lean/README.md) for build instructions.

## Building

The documents are written in [Typst](https://typst.app/). With Typst installed,
build both papers and the presentation from the repository root:

```sh
./build.sh
```

PDFs are placed beside their sources. The script sets the repository as the
Typst project root so documents can import the shared styles. To compile a
single document, use the same root explicitly:

```sh
typst compile --root . papers/analytic-iterates.typ
```

The documents use the Typst packages `touying`, `thmbox`, and `numbly`, which
Typst downloads automatically when needed.

## Commit hook

To compile the papers and presentation automatically before each commit,
enable the repository's versioned Git hooks:

```sh
git config core.hooksPath .githooks
```

The pre-commit hook runs `build.sh` and stages `papers/smooth-iterates.pdf`,
`papers/analytic-iterates.pdf`, and `presentation/slides.pdf` for the current
commit. It blocks the commit if a compilation fails.
