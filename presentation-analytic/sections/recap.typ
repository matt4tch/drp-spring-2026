#import "@preview/touying:0.7.4": *

= Previous DRP

== The question we started with

Suppose $f in C^oo (RR)$ and
$
  f^((n)) (x) -> g(x) quad "for every" x in RR.
$

Must $g$ be smooth, and must $g'=g$?

The previous DRP extended the question from $D=dif/(dif x)$ to
first-order operators $L=a D+b$.

// Presenter prompt: briefly recall the participants and previous talk.

== The MathOverflow post

#image("../../presentation/assets/mathoverflow/question-crop-left-tight.png", height: 250pt)

#text(size: 15pt)[
  Paul Cusson's question; Terence Tao's answer (6 January 2022).
  #link("https://mathoverflow.net/a/413247")[MathOverflow: answer 413247]
]

// Presenter prompt: explain Tao's analyticity result rather than reading the post.

== What the previous DRP established

For $L=a D+b$, with smooth coefficients and $a$ nowhere zero,
$
  (L^n f)(x) -> g(x) quad ==> quad g in C^oo (RR), quad L g=g.
$

A change of variable and an integrating factor turn $L$ into ordinary
differentiation.

*The next question:* what happens for higher-order operators or when the
leading coefficient vanishes?
