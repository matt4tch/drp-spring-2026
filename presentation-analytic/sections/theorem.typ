#import "@preview/touying:0.7.4": *
#import "../../styles/slides.typ": thm

= Proof of Theorem 3.3

== Uniform derivative bounds for the iterates

#thm(variant: [Proposition 3.2 · Local derivative estimates])[
  Let $I$ be an open interval, $m in NN without {0}$, and $L=sum_(j=0)^m a_j D^j$.
  Suppose $f,a_0,dots,a_m$ are real analytic on $I$, $a_m$ is not identically
  zero, and $sup_(n in NN_0) abs((L^n f)(x))<oo$ for every $x in I$.
  For each compact interval $K ⊆ I$, there exist $C,r>0$ such that
  $
    norm((L^n f)^((q)))_K<=C q! r^(-q) quad (n,q in NN_0).
  $
]

Since $(L^n f)(x) -> g(x)$ for every $x in I$, the iterates satisfy the
pointwise boundedness hypothesis.

// Presenter prompt: keep this as a roadmap; add a backup slide for a claim if needed.

== The derivatives converge locally uniformly

#thm(variant: [Lemma 2.2 · Pointwise convergence and local derivative bounds])[
  Suppose $v_n in C^oo (I)$ converge pointwise to $g$ on $I$.
  If $sup_(n in NN_0) norm(v_n^((j)))_K<oo$ for each compact interval
  $K ⊆ I$ and each $j in NN_0$, then $g in C^oo (I)$ and
  $v_n^((j)) -> g^((j))$ locally uniformly on $I$ for every $j in NN_0$.
]

Take $v_n=L^n f$. Theorem 3.3 assumes pointwise convergence, and
Proposition 3.2 supplies the derivative bounds.

== The limit satisfies $L g=g$

#[
  #set text(size: 21pt)
  Fix $x in I$. By Lemma 2.2, for each $0<=j<=m$, $(L^n f)^((j)) (x) -> g^((j)) (x) quad (*)$.
  $
    g(x) & =lim_(n->oo) (L^(n+1) f)(x)                             && "(by pointwise convergence)" \
         & =lim_(n->oo) sum_(j=0)^m a_j (x)(L^n f)^((j)) (x) quad  && ("applying" L "to" L^n f) \
         & =sum_(j=0)^m a_j (x) lim_(n->oo) (L^n f)^((j)) (x) quad && "(by linearity of limits)" \
         & =sum_(j=0)^m a_j (x)g^((j)) (x)                         && ("by" (*)) \
         & =(L g)(x)                                               && ("by definition of" L)
  $

  Since $x in I$ was arbitrary, $L g=g$ on $I$.
]

== Derivative bounds for the limit

Fix $x_0 in I$ and $K=[x_0-s,x_0+s] ⊆ I$, where $s>0$.
For each $q in NN_0$,
$
      & g^((q)) =lim_(n->oo) (L^n f)^((q)) quad "uniformly on" K && "(by Lemma 2.2)" \
  ==> & norm(g^((q)))_K =lim_(n->oo) norm((L^n f)^((q)))_K       && "(by continuity of the sup seminorm)" \
      & norm(g^((q)))_K <=C q! r^(-q)                            && "(by Proposition 3.2)"
$

== The limit equals its Taylor series locally

Fix $x$ with $abs(x-x_0)<min{s,r}$. Since $abs(x-x_0)<s$, every point
between $x_0$ and $x$ lies in $K=[x_0-s,x_0+s]$.
Let $T_N (x)=sum_(q=0)^N frac(g^((q)) (x_0), q!)(x-x_0)^q$. Then
$
  abs(g(x)-T_N (x))
    & <=frac(norm(g^((N+1)))_K,(N+1)!) abs(x-x_0)^(N+1) && "(Taylor remainder bound)" \
    & <=C lr((frac(abs(x-x_0), r)))^(N+1) && ("slide 2.4 with" q=N+1).
$

Since $abs(x-x_0)/r<1$, the bound tends to zero as $N -> oo$.
Thus $T_N (x) -> g(x)$ near every $x_0 in I$, so $g$ is real analytic.
