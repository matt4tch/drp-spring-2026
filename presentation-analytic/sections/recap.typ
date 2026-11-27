#import "@preview/touying:0.7.4": *

= Recap of last time

== The question we started with

Define $L_1 f:=f'$ for $f in C^oo (RR)$. Suppose
$
  (L_1^n f)(x) -> g(x) quad "for every" x in RR.
$
Must $g$ be smooth and satisfy $L_1 g=g$?

// Presenter prompt: briefly recall the participants and previous talk.

== The MathOverflow post

#slide(
  config: config-page(header: none, footer: none, margin: 8pt),
  align: center + horizon,
)[
  #image("../../presentation/assets/mathoverflow/question-crop-left-tight.png", height: 399pt)
  #v(2pt)
  #text(size: 14pt)[Paul Cusson’s MathOverflow question ·
    #link("https://mathoverflow.net/a/413247")[Terence Tao’s answer, 6 January 2022]]
]

// Presenter prompt: explain Tao's analyticity result rather than reading the post.

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
