# Analytic-iterates presentation scaffold

Uses the existing Touying theme and shared slide styles. The earlier deck and paper are unchanged.

Build from the repository root:

```sh
typst compile --root . presentation-analytic/slides.typ presentation-analytic/slides.pdf
```

The outline follows: previous DRP, MathOverflow post, earlier directions, the smooth counterexample and stronger assumptions, Theorem 3.3 and its proof, optional counterexample construction, AI disclosure, discussion.

Edit the section files under `sections/`. Presenter prompts are source comments. Complete the visible AI-disclosure prompts before presenting; they do not assert how AI was used. Set `include-counterexample = false` in `slides.typ` for a shorter talk. The theorem and lemma numbers refer to the current paper and should be rechecked if the paper is reorganized.

The MathOverflow image is reused from `presentation/assets/mathoverflow/`; the source link is on the slide. No copy of the old presentation is required.
