#import "@preview/touying:0.7.4": *

= Proof of Theorem 3.3

== Uniform derivative bounds for the iterates

*Proposition 3.2* requires the iterates to be pointwise bounded.
For each $x in I$, the sequence $(L^n f)(x)$ converges to $g(x)$, so
$
  sup_(n in NN_0) abs((L^n f)(x))<oo quad (x in I).
$

The proposition therefore gives, for each compact interval $K ⊆ I$, constants
$C,r>0$, independent of $n,q$, such that
$
  norm((L^n f)^((q)))_K<=C q! r^(-q)
  quad (n,q in NN_0).
$

// Presenter prompt: keep this as a roadmap; add a backup slide for a claim if needed.

== The derivatives converge locally uniformly

The bound from Proposition 3.2 controls every derivative locally,
uniformly in $n$.

*Lemma 2.2* gives $g in C^oo (I)$ and
$
  (L^n f)^((j)) -> g^((j))
  quad "uniformly on each compact interval" K ⊆ I.
$

In particular,
$
  (L^n f)^((j)) (x) -> g^((j)) (x)
  quad (x in I, j in NN_0).
$

== The limit satisfies $L g=g$

Fix $x in I$. Since $L^(n+1) f -> g$ pointwise,
$
  g(x) & =lim_(n->oo) (L^(n+1) f)(x) \
       & =lim_(n->oo) sum_(j=0)^m a_j (x)(L^n f)^((j)) (x) \
       & =sum_(j=0)^m a_j (x)g^((j)) (x) \
       & =(L g)(x).
$

The sum is finite, and every derivative converges at $x$.
Since $x$ was arbitrary, $L g=g$ on $I$.

== Derivative bounds for the limit

Fix $x_0 in I$ and $K=[x_0-s,x_0+s] ⊆ I$, where $s>0$.
For each $q in NN_0$,
$
  & g^((q)) =lim_(n->oo) (L^n f)^((q)) quad "uniformly on" K
    && "(by Lemma 2.2)" \
  ==> & norm(g^((q)))_K =lim_(n->oo) norm((L^n f)^((q)))_K
    && "(by continuity of the sup seminorm)" \
  & norm(g^((q)))_K <=C q! r^(-q) && "(by Proposition 3.2)"
$

== The limit equals its Taylor series locally

For $abs(x-x_0)<min{s,r}$, Taylor's theorem and the derivative bound give
$
  abs(g(x)-sum_(q=0)^N frac(g^((q)) (x_0), q!)(x-x_0)^q)
  <=C lr((frac(abs(x-x_0), r)))^(N+1) -> 0.
$

Thus $g$ equals its Taylor series near every $x_0 in I$.
