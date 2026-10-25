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

- `drp.typ` — the original mathematical write-up and proofs.
- `slides.typ` — the presentation slides.
- `analytic-continuation.typ` — analytic differential-operator iterates and
  a singular counterexample.
- `continuation.typ` — reading notes for the continuation project.
- `pointwise_iterates_unified.tex` — the earlier AI-generated research draft.
- `analytic-singular-operator-research.md` and
  `undergraduate-continuation-proposal.md` — supporting research notes.
- `lean/` — the Lean formalization of the original results.

## Building

The documents are written in [Typst](https://typst.app/). With Typst installed,
run:

```sh
typst compile drp.typ
typst compile slides.typ
typst compile analytic-continuation.typ
typst compile continuation.typ
```

Each command produces the corresponding PDF in the repository root. The
documents use the Typst packages `touying`, `thmbox`, and `numbly`, which Typst
downloads automatically when needed.

## Commit hook

To compile the presentation and write-up automatically before each commit,
enable the repository's versioned Git hooks:

```sh
git config core.hooksPath .githooks
```

The pre-commit hook regenerates the tracked `slides.pdf` and `drp.pdf` files,
stages them for the current commit, and blocks the commit if Typst is
unavailable or either compilation fails.
