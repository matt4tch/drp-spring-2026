#import "@preview/touying:0.7.4": *
#import themes.university: *

== $L_5 f(x) := x^2 f'(x)$

#new-section-slide(level: 2)[]

=== A second-order zero

#slide(
  config: config-page(margin: (top: 2em, bottom: 1.5em, x: 1.6em)),
  align: top,
  setting: body => {
    set text(size: 23pt)
    set block(spacing: 1.0em)
    pad(top: 0.6em, body)
  },
)[
  Suppose that for every $x in RR$, the limit $g(x) := lim_(n -> oo) L_5^n f(x)$ exists.

  On each of $RR^+$ and $RR^-$, a change of coordinates turns
  $L_5$ into ordinary differentiation, so
  $
    g(x) = C_+ e^(-1/x) quad (x > 0),
    quad
    g(x) = C_- e^(-1/x) quad (x < 0).
  $
  One can show that $C_-$ is forced to be $0$.

  Therefore,
  $
    g(x) = cases(
      C_+ e^(-1/x) space & x > 0,
      0 & x <= 0,
    )
  $
  Thus, $g$ is smooth and $L_5 g = g$.
]
