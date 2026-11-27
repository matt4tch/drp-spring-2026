#import "@preview/touying:0.7.4": *
#import "../../styles/slides.typ": thm

== What can fail when the leading coefficient vanishes

For $h in C^oo (RR)$, define
$
  (L_3 h)(x):=-frac(x^3, 2)h'(x)+(1-x^2)h(x) quad (x in RR).
$
Take the smooth input $f(0)=1$, $f(x)=1-e^(-1/x^2)$ for $x!=0$.
Its iterates satisfy
$
  (L_3^n f)(x) -> cases(1 & "if" x=0, 0 & "if" x!=0).
$
The limit is discontinuous at $0$, so it is not smooth. What if we require the input to be real analytic?

== Strengthening the assumptions

#thm(variant: [Theorem 3.3 · Analytic fixed-point limits])[
  Let $I ⊆ RR$ be a nonempty open interval. Let $m in NN \\ {0}$ and define
  $
    L=sum_(j=0)^m a_j D^j, quad D=L_1,
  $
  where $a_0,dots,a_m$ are real analytic on $I$ and $a_m$ is not
  identically zero. If $f$ is real analytic on $I$ and $L^n f$
  converges pointwise to $g$, then
  + $L g=g$.
  + $g$ is real analytic.
]
