#import "@preview/touying:0.7.4": *
#import themes.university: *

== $L_4 f(x) := x f'(x)$

#new-section-slide(level: 2)[]

=== A simple zero

#slide(
  config: config-page(margin: (top: 2em, bottom: 2em, x: 1.8em)),
  setting: body => {
    set text(size: 24pt)
    set block(spacing: 0.9em)
    body
  },
)[
  Suppose that for every $x in RR$, the limit $ g(x) := lim_(n -> oo) L_4^n f(x) $ exists.

  The rigidity of $L_4$ forces $ f(x)=c_1+c_2 x $ for some $c_1, c_2 in RR$. So, $ g(x)=c_2 x $ for all $x in RR$ and $ L_4 g=g. $
]
