#import "@preview/touying:0.7.4": *

= Constructing the first-order counterexample

== Constructing functions we can iterate

Set $t(x)=1/x^2$, $p(t)=t e^(-t)$, and
$
  w_H (x)=p(t(x))H(t(x)) quad (x!=0).
$

The change-of-variable lemma gives
$
  L w_H=w_(H') quad "on" RR without {0}.
$

Choose $H_n (t)=integral_0^1 s^n e^(s t) dif s$.
Then $H'_n=H_(n+1)$ and $w_(H_0)=f$ away from zero.

// Presenter prompt: show the chain-rule cancellation if time allows.

== The pointwise limit

For $x!=0$, the iterate formula gives
$
  0<=(L^n f)(x)
  =frac(1, x^2) integral_0^1 s^n e^(-(1-s)/x^2) dif s
  <=frac(1, x^2(n+1)) -> 0.
$

At zero, $(L h)(0)=h(0)$, so $(L^n f)(0)=1$ for every $n$.
Thus
$
  (L^n f)(x) -> cases(1 & "if" x=0, 0 & "if" x!=0).
$

The limit is discontinuous, even though every iterate is smooth.
