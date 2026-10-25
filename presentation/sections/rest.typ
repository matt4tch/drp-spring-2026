#import "@preview/touying:0.7.4": *
#import themes.university: *

= Future directions

== Beyond first-order differential operators

#slide(
  config: config-page(margin: (top: 2em, bottom: 1.5em, x: 1.6em)),
  align: top,
  setting: body => {
    set text(size: 21pt)
    set block(spacing: 1.3em)
    pad(top: 0.4em, body)
  },
)[
  The guiding question is:
  $
    lim_(n->oo) L^n f = g "pointwise" quad ==> quad g "is smooth and" L g = g?
  $

  *1. Higher-order ordinary differential operators.*
  $
    L f(x) = sum_(k=0)^m a_k (x) f^((k))(x), quad m >= 2.
  $
  What do we do when the first-order change of coordinates is unavailable?

  *2. Partial differential operators.*
  \ \
  $
    L f(x) = sum_(abs(alpha) <= m) a_alpha (x) partial^alpha f(x)
    quad "on" quad RR^d,
  $
]

#focus-slide[
  Questions?
]
