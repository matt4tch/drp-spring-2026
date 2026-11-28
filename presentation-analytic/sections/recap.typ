#import "@preview/touying:0.7.4": *

= Recap of last time

== The question we started with

#grid(
  columns: (1fr, 1fr),
  column-gutter: 18pt,
  row-gutter: 5pt,
  align: center + horizon,
  link("https://mathoverflow.net/q/413165", image(
    "../../presentation/assets/mathoverflow/paul-cusson-badge.png",
    height: 31pt, alt: "Paul Cusson’s MathOverflow question",
  )),
  link("https://mathoverflow.net/a/413247", image(
    "../../presentation/assets/mathoverflow/terence-tao-badge.png",
    height: 31pt, alt: "Terence Tao’s MathOverflow answer",
  )),
  image("../../presentation/assets/mathoverflow/question-crop-left-tight.png",
    width: 100%, alt: "Paul Cusson’s question on limits of successive derivatives."),
  image("../../presentation/assets/mathoverflow/tao-theorem.png",
    width: 100%, alt: "The analyticity theorem from Terence Tao’s answer."),
)

For $f in C^oo (RR)$, define $L_1 f:=f'$. If $L_1^n f -> g$ pointwise, must $g$ be smooth and satisfy $L_1 g=g$?

== What the previous DRP established

For $L_2=a L_1+b$ and smooth $f,a,b$ with $a$ nowhere zero,
$
  L_2^n f -> g "pointwise" quad ==> quad g in C^oo (RR), quad L_2 g=g.
$

A change of variable and an integrating factor turn the iterates $L_2^n f$
into successive derivatives of a single function. We then apply the
ordinary-derivative result and translate the conclusion back to $g$.

*Two natural generalizations:* what happens when
#enum[
  the leading coefficient is somewhere zero?
][
  the order of the operator exceeds one?
]
