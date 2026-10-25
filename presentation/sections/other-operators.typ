#import "@preview/touying:0.7.4": *
#import themes.university: *
#import "../../styles/slides.typ": section-subtitle

// Record the stronger conclusion for this special case.

== $L_3 f := a f' + b f$

#new-section-slide(level: 2)[
  #section-subtitle[
    $a, b in C^oo (RR)$, with $a$ nowhere zero
  ]
]

=== Absorb the zeroth-order term

#slide(
  config: config-page(margin: (top: 2em, bottom: 1.5em, x: 1.6em)),
  align: top,
  setting: body => {
    set text(size: 23pt)
    set block(spacing: 0.8em)
    pad(top: 0.4em, body)
  },
)[
  Let $a, b in C^oo (RR)$, with $a$ nowhere zero, and suppose
  $ lim_(n->oo) L_3^n f(x)=g(x) $ for every $x in RR$.

  As in the $a f'$ case, define
  $
    Phi(x) := integral_0^x 1/(a(t)) dif t quad (x in RR),
    quad I := Phi(RR).
  $
  $
    w(y) := exp(integral_0^y (b compose Phi^(-1))(s) dif s) quad (y in I),\
    quad F := w dot (f compose Phi^(-1)): I -> RR.
  $
]


=== Iterate derivatives of $F$

#slide(
  config: config-page(margin: (top: 2em, bottom: 1.5em, x: 1.6em)),
  align: top,
  setting: body => {
    set text(size: 22pt)
    set block(spacing: 0.9em)
    pad(top: 0.4em, body)
  },
)[
  Similarly, for $n>=0$,
  $
    F^((n)) = w dot (L_3^n f) compose Phi^(-1)
  $

  Therefore, the pointwise limit
  $
    G(y) & := lim_(n->oo) F^((n))(y) \
         & = lim_(n->oo) w(y) dot (L^n_3 f)(Phi^(-1)(y)) \
         & = w(y) dot g(Phi^(-1)(y)).
  $
  exists. As before, we have $G'=G$, so $L_3 g = g.$ Moreover, $ g= (G compose Phi)/(w compose Phi) $ so $g$ is smooth.
]
