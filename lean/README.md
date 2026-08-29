# Lean formalization

This directory is a self-contained Lean/Mathlib project for the Spring 2026
DRP project, *Iteration of Linear Differential Operators*.

## Layout

- `DRPSpring2026/Analyticity/Tao.lean` states Tao's analyticity theorem and
  defines what it means for a real function to extend to an entire function.
- `DRPSpring2026/Analyticity/Estimates.lean` contains the reusable exponential
  Taylor-series estimate for globally analytic functions.
- `DRPSpring2026/IteratedDerivative/Limit.lean` states the ordinary-derivative
  application: a pointwise limit of iterated derivatives is smooth and fixed
  by differentiation.
- `DRPSpring2026.lean` is the umbrella import for the formalization.

Tao's analyticity theorem and its ordinary-derivative application are fully
proved using the Baire-category argument, Taylor-series estimates, the
Fundamental Theorem of Calculus, and dominated convergence from the write-up.
Future differential-operator results should live in
`DRPSpring2026/Operators/` and build on the ordinary-derivative result.

## Building

From this directory, run:

```sh
lake update
lake build
```
