#import "@preview/touying:0.7.4": *

= Proof of Theorem 3.3

== The estimate behind the proof

Pointwise convergence implies
$
  sup_(n in NN_0) abs((L^n f)(x))<oo quad (x in I).
$

*Proposition 3.2:* for each compact interval $K ⊆ I$, there exist
$C,r>0$, independent of $n,q$, such that
$
  norm((L^n f)^((q)))_K<=C q! r^(-q)
  quad (n,q in NN_0).
$

// Presenter prompt: keep this as a roadmap; add a backup slide for a claim if needed.

== Part 1: convergence of the derivatives

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

== Part 1: the fixed-point equation

Fix $x in I$. Since $L^(n+1) f -> g$ pointwise,
$
  g(x) & =lim_(n->oo) (L^(n+1) f)(x) \
       & =lim_(n->oo) sum_(j=0)^m a_j (x)(L^n f)^((j)) (x) \
       & =sum_(j=0)^m a_j (x)g^((j)) (x) \
       & =(L g)(x).
$

The sum is finite, and every derivative converges at $x$.
Since $x$ was arbitrary, $L g=g$ on $I$.

== Part 2: the Taylor remainder

Fix $x_0 in I$ and $K=[x_0-s,x_0+s] ⊆ I$, where $s>0$.
Uniform derivative convergence gives
$
  norm(g^((q)))_K
  =lim_(n->oo) norm((L^n f)^((q)))_K<=C q! r^(-q).
$

For $abs(x-x_0)<min{s,r}$, Taylor's theorem gives
$
  abs(g(x)-sum_(q=0)^N frac(g^((q)) (x_0), q!)(x-x_0)^q)
  <=C lr((frac(abs(x-x_0), r)))^(N+1) -> 0.
$

Thus $g$ equals its Taylor series near every $x_0 in I$.
