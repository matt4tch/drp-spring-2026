#import "@preview/touying:0.7.4": *
#import "../../styles/slides.typ": intro-border, intro-paper, nospace, theme-primary, theme-secondary, thm

= The original problem

#slide(
  config: config-page(
    fill: intro-paper,
    margin: 1em,
    header: none,
    footer: none,
  ),
  align: horizon,
)[
  #set text(fill: theme-primary, weight: "regular")
  #align(center)[
    #block(
      fill: white,
      stroke: 0.8pt + intro-border,
      radius: 8pt,
      inset: 4pt,
    )[
      #image(
        "../assets/mathoverflow/question-crop-left-tight.png",
        width: 650pt,
      )

      #place(bottom + right, dx: -12pt, dy: -12pt)[
        #block(
          width: 215pt,
          fill: white,
          stroke: 1.2pt + theme-secondary,
          radius: 7pt,
          inset: 4pt,
        )[
          #image(
            "../assets/mathoverflow/paul-cusson-badge.png",
            width: 207pt,
          )
        ]
      ]
    ]
  ]
]

== The original question

Let $f in C^oo (RR)$, and write
$
  L_1 := frac(dif, dif x).
$

Suppose that for every $x in RR$ the pointwise limit
$
  g(x) := lim_(n -> oo) L_1^n f(x)
$
exists.

#strong[Question.] Must $g$ be smooth? Moreover, can we prove $L_1 g=g$?

#slide(
  config: config-page(
    fill: intro-paper,
    margin: 1em,
    header: none,
    footer: none,
  ),
  align: horizon,
)[
  #set text(fill: theme-primary, weight: "regular")
  #align(center)[
    #stack(
      dir: ttb,
      spacing: 12pt,
      align(center)[
        #text(size: 22pt, weight: "bold")[
          A direct answer:
        ]
      ],
      block(
        fill: white,
        stroke: 0.8pt + intro-border,
        radius: 8pt,
        inset: 4pt,
      )[
        #image(
          "../assets/mathoverflow/tao-theorem.png",
          width: 640pt,
        )
      ],
      block(width: 650pt)[
        #grid(
          columns: (1fr, 155pt),
          column-gutter: 18pt,
          align: horizon,
          [
            #text(size: 16pt, weight: "bold")[
              The convergence hypothesis actually forces $f$ to be a restriction of an entire function.
            ]
          ],
          [
            #block(
              width: 155pt,
              fill: white,
              stroke: 1.2pt + theme-secondary,
              radius: 7pt,
              inset: 4pt,
            )[
              #image(
                "../assets/mathoverflow/terence-tao-badge.png",
                width: 147pt,
              )
            ]
          ],
        )
      ],
    )
  ]
]

== Tao's analyticity theorem

// State the theorem and outline its role in the original problem.
#thm[
  Let $f in C^oo (RR)$, and suppose that for every $x in RR$,
  $
    M(x) := sup_(m >= 0) abs(f^((m)) (x)) < oo.
  $
  Then $f$ is the restriction to $RR$ of an entire function. Equivalently,
  $f$ is real analytic with infinite radius of convergence.
]

== Why Tao's theorem applies

For each fixed $x in RR$, the sequence
$
  (f^((n))(x))nospace_(n=0)^oo
$
converges, hence is bounded. Therefore
$
  M(x) = sup_(n>=0) abs(f^((n))(x)) < oo,
$
so Tao's theorem applies immediately: $f$ is the restriction of an entire
function.

== A locally uniform bound

Since $f$ is the restriction of an entire function, expand $f^((k))$ at $0$. Every coefficient is
controlled by the _single_ number $M(0)$:
$
                 f^((k))(x) & = sum_(n=0)^oo (f^((n+k))(0))/(n!) x^n, \
  ==> space abs(f^((k))(x)) & <= sum_(n=0)^oo M(0)/(n!) abs(x)^n
                              = M(0) e^(abs(x)).
$

Note that for all $n in NN$ and $x in [a,b]$,

$
  abs(f^((n))(x)) <= C_([a,b]) := sup_(x in [a,b]) M(0) e^(abs(x)) < oo.
$

== Take the limit on both sides

#slide(
  config: config-page(margin: (top: 2em, bottom: 2em, x: 1.6em)),
  setting: body => {
    set text(size: 23pt)
    set block(spacing: 0.9em)
    body
  },
)[
  Fix $a<b$. For every $n$, the Fundamental Theorem of Calculus gives the identity
  $
    f^((n))(b)-f^((n))(a)
    = integral_a^b f^((n+1))(x) dif x
  $
  Taking $n -> oo$ on both sides and applying LDCT to the right-hand side,
  $
        && lim_(n->oo) (f^((n))(b)-f^((n))(a)) & = lim_(n -> oo) integral_a^b f^((n+1))(x) dif x \
    ==> &&                     space g(b)-g(a) & = integral_a^b lim_(n -> oo) f^((n+1))(x) dif x \
        &&                                     & = integral_a^b g(x) dif x.
  $
]

== The limit is continuous

#slide(
  config: config-page(margin: (top: 2em, bottom: 2em, x: 1.6em)),
  setting: body => {
    set text(size: 26pt)
    set block(spacing: 1.5em)
    body
  },
)[
  Since $g$ is the pointwise limit of the derivatives and
  $abs(f^((n))(x)) <= C_([a,b])$, we also have
  $abs(g(x)) <= C_([a,b])$ on $[a,b]$. Therefore,
  $
    abs(g(b)-g(a)) & <= integral_a^b abs(g(x)) dif x \
                   & <= C_([a,b]) abs(b-a).
  $

  Thus $g$ is locally Lipschitz, and hence continuous.
]

== The limit satisfies $L_1 g=g$

#slide(
  config: config-page(margin: (top: 2em, bottom: 2em, x: 1.6em)),
  setting: body => {
    set text(size: 26pt)
    set block(spacing: 0.77em)
    body
  },
)[
  Fix $a$. The integral identity becomes
  $
    g(x) = g(a) + integral_a^x g(t) dif t.
  $
  Since $g$ is continuous, the Fundamental Theorem of Calculus yields
  $
    g'(x) = g(x).
  $

  Thus $L_1 g = g$, so $g$ is smooth. Solving the ODE gives
  $
    g(x) = C e^x
  $
  for some $C in RR$.
]
