#import "../styles/paper.typ": *

#show: preamble
#show: setup-shared-counters(2)
#show: project-header

#set document(
  title: "Pointwise Limits of Differential-Operator Iterates: Analytic Input and a Singular Counterexample",
  author: ("Jake Edmonstone", "Matthew Tchouikine"),
)

#notes-title("Pointwise Limits of Differential-Operator Iterates")
#align(center)[
  #text(19pt)[Analytic Input and a Singular Counterexample] \
  #v(0.6em)
  #strong[Jake Edmonstone and Matthew Tchouikine] \
  Mentor: Paul Cusson \
  University of Waterloo Directed Research Program
]

#v(1em)
*Abstract.* Let $L$ be a linear differential operator of positive order
with real-analytic coefficients on an open interval, allowing zeros
of the leading coefficient. For real-analytic input $f$, we prove
that pointwise boundedness of $(L^n f)$ implies local uniform bounds
on every derivative of the iterates. If the orbit converges pointwise,
its limit $g$ is real analytic, the convergence holds locally uniformly
with all derivatives, and $L g=g$. For one such first-order operator
with polynomial coefficients, we construct a smooth, nonanalytic input
whose iterates converge to the indicator of the origin.

#outline()
#pagebreak()

= Introduction

== Background and results

Our previous work @drp studied the following question of
Paul Cusson @tao.

#problem[Pointwise limits of successive derivatives][
  Suppose $f in C^oo (RR)$ and $f^((n)) (x) -> g(x)$ for every real $x$.
  Must $g$ be differentiable, and must $g'=g$?
]

Tao's analyticity theorem @tao gives an affirmative answer: pointwise
boundedness of all derivatives forces an entire extension of $f$ and
local uniform derivative bounds. These bounds justify passing to the
limit in $f^((n+1))=D f^((n))$.

The first-order theorem @drp[Section 2] treats
$L h=a h'+b h$, where $a,b in C^oo (RR)$ and $a$ is nowhere zero.
A change of variable and an integrating factor turn repeated
application of $L$ into repeated ordinary differentiation. For
$f in C^oo (RR)$, pointwise convergence of $L^n f$ therefore implies
that the limit is smooth and satisfies $L g=g$.

In @thm:analytic-convergence we consider operators of arbitrary
positive order with analytic coefficients and input, allowing zeros
of the leading coefficient.
Pointwise boundedness of the orbit gives
local uniform bounds on every derivative by @prop:analytic-bounds;
pointwise convergence
then gives a real-analytic limit satisfying $L g=g$. The proof
obtains bounds on one real interval, propagates them along complex
paths avoiding the zeros, and uses the maximum-modulus principle
to extend the bounds across those zeros.

In @thm:counterexample, a first-order operator with polynomial
coefficients and a single zero of its leading coefficient has a smooth
input whose orbit converges to a discontinuous limit. This shows that
the analytic-input assumption in @thm:analytic-convergence cannot be
replaced by smoothness. It also shows that the nowhere-zero hypothesis
in the smooth first-order theorem cannot be omitted.

== Notation

Throughout, $I subs RR$ is a nonempty open interval. Inputs and
coefficients on $I$ are real valued. Holomorphic extensions are denoted
by the same symbols as the original functions. Write $NN={1,2,3,dots}$, $NN_0={0,1,2,dots}$,
$D=frac(dif, dif x)$, and $h^((0))=h$. For an operator
$
  L h=sum_(j=0)^m a_j h^((j)),
$
write $L^0 f=f$. Thus $L(L^n f)=L^(n+1) f$ for $n in NN_0$.

For a continuous function $h$ on a nonempty compact set $K$, put
$norm(h)_K=sup_(x in K) abs(h(x))$. We say that $v_n$ converges to $g$
*locally uniformly with all derivatives* if $g$ is smooth and
$
  norm(v_n^((q))-g^((q)))_K toinf(n) 0
  quad "for every" q in NN_0 "and every compact interval" K subs I.
$
We write $v_n -> g$ in $C^oo_("loc") (I)$ for this convergence.
In the complex plane, $D(z,R)={w in CC st abs(w-z)<R}$ denotes an
open disk, and $overline(D(z,R))$ its closure.

= Elementary estimates

== Interpolation

#lemma[Scaled interpolation][
  Fix $m in NN$. There is a constant $C_m$, depending only
  on $m$, such that for every compact interval $J=[alpha,beta]$ with
  $alpha<beta$, every real function $h$ of class $C^m$ on a neighborhood
  of $J$, and
  $0<delta<=frac(beta-alpha, 2m)$,
  $
    norm(h^((j)))_J
    <= C_m delta^(-j) norm(h)_J
    +C_m delta^(m-j) norm(h^((m)))_J
    quad (0<=j<m).
  $
]<lem:interpolation>

#pf[
  Fix $x in J$. Choose $epsilon=1$ if $x<=frac(alpha+beta, 2)$,
  and $epsilon=-1$ otherwise. Then all points $x+epsilon ell delta$,
  $1<=ell<=m$, lie in $J$. Taylor's theorem gives
  $
    h(x+epsilon ell delta)
    =sum_(j=0)^(m-1) frac((epsilon ell)^j, j!) delta^j h^((j)) (x)+R_ell,
  $
  where
  $
    abs(R_ell)<=frac((m delta)^m, m!) norm(h^((m)))_J.
  $
  These are $m$ linear equations for the unknowns
  $delta^j h^((j)) (x)$, $0<=j<m$. Their coefficient matrix has
  entries $V_(ell,j)=frac((epsilon ell)^j, j!)$.

  If $V v=0$, the polynomial
  $p(t)=sum_(j=0)^(m-1) frac(v_j, j!)t^j$ vanishes at the $m$
  distinct points $epsilon,2epsilon,dots,m epsilon$. Since its degree
  is at most $m-1$, it is zero. Thus $V$ is invertible.

  Let $A_m$ be the maximum sum of absolute values of entries in a
  row of $V^(-1)$, over both choices of $epsilon$. Multiplication by
  $V^(-1)$ gives
  $
    abs(h^((j)) (x))
    <= A_m delta^(-j)
    (norm(h)_J+frac((m delta)^m, m!) norm(h^((m)))_J).
  $
  Take the supremum over $x in J$ and set
  $C_m=A_m max{1,frac(m^m, m!)}$.
]

We will also use the following first-derivative estimate. Let $J$ be
a compact interval and let $h$ be twice continuously differentiable
on a neighborhood of $J$. If $t>0$ and $[x,x+t] subs J$, Taylor's
theorem gives
$
  abs(h'(x))
  <= frac(2, t) norm(h)_J+frac(t, 2) norm(h'')_J.
$
Indeed, subtract $h(x)$ from the formula for $h(x+t)$ and divide by $t$.

== Smooth convergence

#lemma[Pointwise convergence and local derivative bounds][
  Suppose $v_n in C^oo (I)$ and $v_n (x) -> g(x)$ for every $x in I$.
  Assume that for every compact interval $J subs I$ and every $j in NN_0$
  there is a finite constant $B_(J,j)$ such that
  $
    norm(v_n^((j)))_J<=B_(J,j) quad "for every" n.
  $
  Then $g$ is smooth and $v_n -> g$ locally uniformly with all derivatives.
]<lem:convergence>

#pf[
  *First, the functions converge uniformly on compact intervals.* Fix
  a compact interval $K subs I$ and let $B=B_(K,1)$. The mean value
  theorem gives
  $
    abs(v_n (x)-v_n (y))<=B abs(x-y) quad (x,y in K).
  $
  Given $epsilon>0$, choose $delta>0$ with $2B delta<epsilon/2$.
  Cover $K$ by finitely many intervals of radius $delta$ centered at
  points $x_1,dots,x_q$ of $K$. At these finitely many points,
  pointwise convergence gives one $N$ such that
  $
    abs(v_n (x_i)-v_m (x_i))<epsilon/2
    quad (n,m>=N, 1<=i<=q).
  $
  For any $x in K$, choose $x_i$ within $delta$ of $x$. The triangle
  inequality gives
  $
    abs(v_n (x)-v_m (x))<2B delta+epsilon/2<epsilon.
  $
  Thus $(v_n)$ is uniformly Cauchy on $K$. Letting $m$ tend to infinity
  shows uniform convergence to its pointwise limit $g$. In particular,
  $g$ is continuous.

  *Next, the derivatives are uniformly Cauchy as well.* Suppose that
  $(v_n^((j)))$ is uniformly Cauchy on every compact interval. Choose
  $K=[c,d]$ and a larger $J=[a,b] subs I$ with $a<c<=d<b$.
  Apply the preceding first-derivative estimate to
  $h=v_n^((j))-v_m^((j))$. For $0<t<b-d$ it gives
  $
    norm(v_n^((j+1))-v_m^((j+1)))_K
    <= frac(2, t) norm(v_n^((j))-v_m^((j)))_J
    +t B_(J,j+2).
  $
  Given $epsilon>0$, first fix $t$ small enough that the last term is
  less than $epsilon/2$. The induction hypothesis then makes the first
  term less than $epsilon/2$ for all sufficiently large $n,m$.
  This proves the induction step. Starting at $j=0$, all derivative
  sequences converge uniformly on compact intervals. Denote their
  continuous limits by $g_j$, with $g_0=g$.

  *Finally, identify these limits as derivatives.* For $x,y in I$,
  the fundamental theorem of calculus gives
  $
    v_n^((j)) (y)-v_n^((j)) (x)
    =integral_x^y v_n^((j+1)) (s) dif s.
  $
  Uniform convergence on the interval between $x$ and $y$ permits
  passage to the limit, so
  $
    g_j (y)-g_j (x)=integral_x^y g_(j+1) (s) dif s.
  $
  Since $g_(j+1)$ is continuous, this identity implies
  $g_j '=g_(j+1)$. Induction gives $g_j=g^((j))$ for every $j$.
]

= Analytic coefficients and input

== Uniform propagation on a complex disk

Away from a zero of the leading coefficient, the relation
$L(L^n f)=L^(n+1) f$ expresses $(L^n f)^((m))$ in terms of $L^(n+1) f$ and the
lower derivatives of $L^n f$. The following lemma propagates a bound
for these functions from the center of a disk to a smaller disk.
The smaller radius depends only on the coefficients and the original
radius, so it can be used uniformly along a fixed path.

#lemma[Uniform propagation][
  Fix $m in NN$, a radius $R>0$, and $z_* in CC$. Suppose that
  $c,b_0,dots,b_(m-1)$ and the functions $v_(n,j)$,
  $n in NN_0$, $0<=j<m$, are holomorphic on a common neighborhood
  of $overline(D(z_*,R))$ and satisfy
  $
      v'_(n,j) & = v_(n,j+1) quad (0<=j<m-1), \
    v'_(n,m-1) & = c v_(n+1,0)+sum_(j=0)^(m-1)b_j v_(n,j).
  $
  Put $E=overline(D(z_*,R))$. Choose
  $
    C_0>=max{1,norm(c)_E+sum_(j=0)^(m-1)norm(b_j)_E},
    quad A=max{2/R,2C_0}.
  $
  If a finite constant $M>=0$ satisfies
  $abs(v_(n,j) (z_*))<=M$ for all $n,j$, then
  $
    abs(v_(n,j) (z))<=2M
    quad "whenever" abs(z-z_*)<=frac(1, 2A),
  $
  for every $n in NN_0$ and $0<=j<m$.
]<lem:propagation>

#pf[
  Expand at $z_*$:
  $
    v_(n,j) (z) & =sum_(k=0)^oo d_(n,j,k) (z-z_*)^k, \
           c(z) & =sum_(ell=0)^oo c_ell (z-z_*)^ell,
                  quad b_j (z)=sum_(ell=0)^oo b_(j,ell) (z-z_*)^ell.
  $
  Cauchy's estimates give
  $
    abs(c_ell)+sum_(j=0)^(m-1)abs(b_(j,ell))<=C_0 R^(-ell).
  $
  Set $T_k=sup_(n in NN_0,0<=j<m)abs(d_(n,j,k))$, initially allowing
  the value $oo$. The hypothesis gives $T_0<=M$.
  Comparing coefficients in the differential relations, we obtain
  $
      (k+1)d_(n,j,k+1) & =d_(n,j+1,k) quad (j<m-1), \
    (k+1)d_(n,m-1,k+1) & =sum_(ell=0)^k lr(
                           (c_ell d_(n+1,0,k-ell)
                             +sum_(j=0)^(m-1)b_(j,ell)d_(n,j,k-ell))
                         ).
  $
  Consequently, whenever $T_0,dots,T_k$ are finite,
  $
    (k+1)T_(k+1)<=C_0 sum_(ell=0)^k R^(-ell)T_(k-ell).
  $
  For the first set of relations, the $ell=0$ term suffices,
  since $C_0>=1$. For the last relation, use the coefficient bound
  above. This also proves inductively that every $T_k$ is finite.

  We claim that $T_k<=M A^k$ for all $k in NN_0$. It holds at $k=0$.
  Assuming it through degree $k$ and using $R A>=2$, we get
  $
    (k+1)T_(k+1) & <=C_0 M A^k sum_(ell=0)^k (R A)^(-ell) \
                 & <=2C_0 M A^k<=M A^(k+1).
  $
  Since $k+1>=1$, this proves the induction step.
  The Taylor series of every $v_(n,j)$ represents it on $D(z_*,R)$,
  and $frac(1, 2A)<=R/4$. Hence, for $abs(z-z_*)<=frac(1, 2A)$,
  $
    abs(v_(n,j) (z))
    <=sum_(k=0)^oo M A^k abs(z-z_*)^k<=2M.
  $
]

== Local derivative estimates

#prop[Local derivative estimates][
  Let $m in NN$ and define
  $
    L=sum_(j=0)^m a_j D^j,
  $
  where $a_0,dots,a_m$ are real analytic on $I$ and $a_m$ is not
  identically zero. Let $f$ be real analytic on $I$ and suppose that
  $
    sup_(n in NN_0)abs((L^n f)(x))<oo quad "for every" x in I.
  $
  Then, for every compact interval $K subs I$, there are constants
  $C,r>0$ such that
  $
    norm((L^n f)^((q)))_K<=C q! r^(-q)
    quad (n,q in NN_0).
  $
]<prop:analytic-bounds>

#pf[
  #block(breakable: false)[
    *Claim 1*: There exist $x_* in I$ with $a_m (x_*)!=0$ and $M_*>0$
    such that
    $
      abs((L^n f)^((j)) (x_*))<=M_*
      quad "for all" n in NN_0, 0<=j<m.
    $
  ]

  *Proof of Claim 1*: Since $a_m$ is not identically zero, there is a compact interval
  $J_0=[alpha_0,beta_0] subs I$, with $alpha_0<beta_0$, on which
  $a_m$ does not vanish. For each $N in NN$, define
  $
    E_N:={x in J_0 st abs((L^n f)(x))<=N "for every" n in NN_0}.
  $
  Note that $E_N$ is closed and ${E_n}_(n in NN)$ covers $J_0$. Baire Category Theorem gives an
  $N in NN$ with $op("int")_(J_0) (E_N)!=em$. Hence there are
  $x in J_0$ and $epsilon>0$ such that
  $
    (x-epsilon,x+epsilon) ∩ J_0 subs E_N.
  $
  Since $J_0$ is a nondegenerate interval, this intersection is an interval
  of positive length. It therefore contains a compact interval
  $J=[alpha,beta] subs E_N$ with $alpha<beta$. Thus
  $norm(L^n f)_J<=N$ for all $n in NN_0$.

  On $J$, the equation $L(L^n f)=L^(n+1) f$ gives
  $
    (L^n f)^((m))=frac(L^(n+1) f, a_m)
    -sum_(j=0)^(m-1)frac(a_j, a_m)(L^n f)^((j)).
  $
  Since $f$ and the coefficients of $L$ are real analytic on $I$,
  every $L^n f$ is real analytic on $I$, hence belongs to $C^m (I)$.
  Since $J subs I$ and $I$ is open, @lem:interpolation applies to each $L^n f$.
  For $0<delta<=frac(beta-alpha, 2m)$, this yields
  $
    norm((L^n f)^((m)))_J & <=N norm(frac(1, a_m))_J
                            +C_m N sum_(j=0)^(m-1)norm(frac(a_j, a_m))_J delta^(-j) \
                          & quad +C_m norm((L^n f)^((m)))_J
                            sum_(j=0)^(m-1)norm(frac(a_j, a_m))_J delta^(m-j).
  $
  All powers $m-j$ in the last sum are positive. Choose a fixed
  $delta>0$ small enough that the coefficient of
  $norm((L^n f)^((m)))_J$ on the right is at most $1/2$. This norm is
  finite for each $n$, since $(L^n f)^((m))$ is continuous on the
  compact interval $J$. Subtracting $frac(1, 2) norm((L^n f)^((m)))_J$
  from both sides of the resulting inequality gives
  $
    frac(1, 2) norm((L^n f)^((m)))_J
    <=N norm(frac(1, a_m))_J
    +C_m N sum_(j=0)^(m-1)norm(frac(a_j, a_m))_J delta^(-j).
  $
  Multiplying both sides by $2$, we obtain
  $
    norm((L^n f)^((m)))_J
    <=2N norm(frac(1, a_m))_J
    +2C_m N sum_(j=0)^(m-1)norm(frac(a_j, a_m))_J delta^(-j).
  $
  This bound is independent of $n$. Applying @lem:interpolation again bounds
  $norm((L^n f)^((j)))_J$ uniformly in $n$ for every $0<=j<m$.
  In particular, at a chosen
  $x_* in (alpha,beta)$,
  $
    abs((L^n f)^((j)) (x_*))<=M_*
    quad "for all" n in NN_0, 0<=j<m.
  $
  for some $M_*>0$. Since $a_m$ does not vanish on $J$, we also have
  $a_m (x_*)!=0$. $square.stroked$

  *Claim 2*. There is a connected open set $Omega subs CC$ containing $I$
  on which $f,a_0,dots,a_m$ and every iterate $L^n f$ have holomorphic extensions.

  *Proof of Claim 2*: Fix $x in I$. For each $h in {f,a_0,dots,a_m}$,
  real analyticity gives $R_h>0$ such that $(x-R_h,x+R_h) subs I$ and
  $
    h(t)=sum_(k=0)^oo c_(h,k) (t-x)^k
    quad "for" abs(t-x)<R_h.
  $
  Choose $0<rho_h<R_h$. Since the series converges at $t=x+rho_h$,
  its terms are bounded, so there is $M_h>0$ such that
  $abs(c_(h,k)) rho_h^k<=M_h$ for all $k in NN_0$. For complex $z$ with
  $abs(z-x)<rho_h$, we therefore have
  $
    abs(c_(h,k) (z-x)^k)<=M_h lr((frac(abs(z-x), rho_h)))^k.
  $
  Comparison with a geometric series shows that
  $sum_(k=0)^oo c_(h,k) (z-x)^k$ converges absolutely on $D(x,rho_h)$.
  By the theorem on differentiation of power series, its sum is
  holomorphic on this disk and agrees with $h$ on its real diameter.
  Since there are only finitely many functions $f,a_0,dots,a_m$,
  we can choose $r_x>0$ smaller than all their radii $rho_h$.
  Thus they have holomorphic extensions on the common disk $D(x,r_x)$,
  whose real diameter is contained in $I$.

  Let $Omega=union.big_(x in I) D(x,r_x)$. This is an open set containing $I$.
  If two of these disks intersect,
  their intersection contains a real interval. The extensions agree
  on that interval, hence on the intersection by the identity
  theorem. They therefore define holomorphic functions on $Omega$.
  The interval $I$ is connected, and every disk $D(x,r_x)$ is connected
  and contains its center $x in I$. Thus
  $
    Omega=I union union.big_(x in I) D(x,r_x)
  $
  is connected as it is the union of the connected set $I$ with connected
  sets that each have nonempty intersection with $I$.

  Differentiation and multiplication preserve holomorphy on $Omega$,
  so all iterates $L^n f$ are holomorphic on this same domain. $square.stroked$

  *Claim 3*. The family ${L^n f}_(n in NN_0)$ is locally bounded on $Omega$.

  *Proof of Claim 3*: By Claim 2, $a_m$ is holomorphic on the connected
  open set $Omega$. Since it is not identically zero, the zero set
  $
    Z={z in Omega st a_m (z)=0}
  $
  has no accumulation point in $Omega$ and is closed in $Omega$.

  First, we prove local boundedness at every point of $Omega without Z$.
  By Claim 1, we may fix $x_* in I without Z$ and $M_*>0$ satisfying
  the bounds in that claim.

  The domain $Omega without Z$ is path
  connected. Indeed, two points can be joined by a polygonal path
  in $Omega$. Its compact image meets only finitely many zeros,
  and small detours around those zeros give a path in $Omega without Z$.

  Fix $z in Omega without Z$ and a continuous path from $x_*$ to
  $z$ in this domain. Its image $Gamma$ is compact. Choose $R>0$
  small enough that the compact set
  $
    E=union.big_(w in Gamma)overline(D(w,R))
  $
  is contained in $Omega without Z$. To apply @lem:propagation, set
  $
    c=frac(1, a_m), quad b_j=-frac(a_j, a_m),
    quad v_(n,j)=(L^n f)^((j)) quad (0<=j<m).
  $
  For every $n in NN_0$ and $0<=j<m-1$, the definition gives
  $
    v'_(n,j)=((L^n f)^((j)))'=(L^n f)^((j+1))=v_(n,j+1).
  $
  Also, $L(L^n f)=L^(n+1) f$ on $Omega$, so on $Omega without Z$,
  $
    v'_(n,m-1) & =(L^n f)^((m)) \
               & =frac(L^(n+1) f, a_m)
                 -sum_(j=0)^(m-1)frac(a_j, a_m)(L^n f)^((j)) \
               & =c v_(n+1,0)+sum_(j=0)^(m-1)b_j v_(n,j).
  $
  Thus the derivative identities required by @lem:propagation hold.
  By Claim 2, all $v_(n,j)$ are holomorphic on $Omega$.
  Since $a_m$ has no zeros on $Omega without Z$, the coefficients
  $c,b_0,dots,b_(m-1)$ are holomorphic there and hence bounded on the
  compact set $E$. Set
  $
    C_0=max{1,norm(c)_E+sum_(j=0)^(m-1)norm(b_j)_E},
    quad A=max{2/R,2C_0}.
  $
  These choices satisfy @lem:propagation on every disk of radius
  $R$ centered on the path.

  Uniform continuity of the path allows a finite subdivision whose
  consecutive centers have distance less than $frac(1, 2A)$.
  Starting with the bound $M_*$ at $x_*$, each application gives
  a bound on the next disk at most twice the preceding bound.
  After finitely many steps, all iterates $L^n f$ are uniformly bounded
  on a neighborhood of $z$. Thus the family ${L^n f}_(n in NN_0)$ is locally
  bounded on $Omega without Z$.

  Next, we prove local boundedness at every point of $Z$.
  Fix $z_0 in Z$. Choose $rho>0$ such that
  $overline(D(z_0,rho)) subs Omega$ and this disk contains no other
  zero. Its boundary circle is a compact subset of $Omega without Z$.
  By the first step, every point of this boundary circle has a neighborhood
  on which all $L^n f$ are bounded by a common constant independent of $n$.
  Compactness gives a finite cover by these neighborhoods, hence
  a constant $C$ such that
  $
    abs((L^n f)(z))<=C
    quad (n in NN_0, abs(z-z_0)=rho).
  $
  By Claim 2, every $L^n f$ is holomorphic on a neighborhood of the closed disk,
  including at $z_0$. The maximum-modulus principle gives
  $
    abs((L^n f)(z))<=C
    quad (n in NN_0, abs(z-z_0)<=rho).
  $
  This bounds all $L^n f$ on the neighborhood $D(z_0,rho)$ of $z_0$,
  so the family is locally bounded at $z_0$. Since $z_0 in Z$ was arbitrary,
  the family is locally bounded at every point of $Z$.
  Together with the first step, this proves local boundedness on all of
  $Omega$. $square.stroked$

  We now prove the proposition. Let $K subs I$ be a compact interval.
  By Claim 2, $Omega$ is an open neighborhood of $K$, so we can choose
  $r>0$ such that the closed complex $r$-neighborhood of $K$ is
  contained in $Omega$. By Claim 3, local boundedness and a finite cover give
  a constant $C_K>0$ bounding every $L^n f$ on this compact neighborhood.
  Cauchy's estimates on disks of radius $r$ centered at $x in K$ give
  $
    norm((L^n f)^((q)))_K<=C_K q! r^(-q)
    quad (n,q in NN_0).
  $
  This proves the estimate.
]


== Analytic fixed-point limits

#thm[Analytic fixed-point limits][
  Let $m in NN$ and define
  $
    L=sum_(j=0)^m a_j D^j,
  $
  where $a_0,dots,a_m$ are real analytic on $I$ and $a_m$ is not
  identically zero. If $f$ is real analytic on $I$ and $L^n f$
  converges pointwise to $g$, then
  #enum[
    $L g = g$
  ][
    $g$ is real analytic
  ]
]<thm:analytic-convergence>

#text(style: "oblique", weight: "bold")[Proof:]
#block[
  #enum[
    Since $L^n f -> g$ pointwise, $((L^n f)(x))_(n in NN_0)$ is bounded for all $x in I$, so $sup_(n in NN_0) abs((L^n f)(x))<oo$. Hence, @prop:analytic-bounds applies, and we obtain that for every compact interval $K subs I$, there exist $C,r>0$ such that
    $
      norm((L^n f)^((q)))_K <= C q! r^(-q)
      quad "for all" n,q in NN_0. quad (suit.heart)
    $
    Therefore, @lem:convergence applies, and we obtain that $g$ is smooth and that $(L^n f)^((j)) -> g^((j))$ locally uniformly on $I$ for all $j in NN_0$ $(circle.filled)$. Locally uniform convergence implies pointwise convergence, so
    $
      (L^n f)^((j)) (x) -> g^((j)) (x)
      quad "for every" x in I "and every" j in NN_0. quad (diamond.filled)
    $
    Fix $x in I$. Then
    $
                                      lim_(n->oo) (L(L^n f))(x) & = lim_(n->oo) (L^(n+1) f)(x) \
      ==> lim_(n->oo) sum_(j=0)^m a_j (x) dot (L^n f)^((j)) (x) & = g(x) quad "(since" (L^(n+1) f)(x) -> g(x)")" \
      ==> sum_(j=0)^m a_j (x) dot lim_(n->oo) (L^n f)^((j)) (x) & = g(x) \
                        ==> sum_(j=0)^m a_j (x) dot g^((j)) (x) & = g(x) quad "(by" diamond.filled")" \
                                                   ==> (L g)(x) & = g(x).
    $
    Since $x in I$ was arbitrary, $L g=g$, as desired.

  ][
    Fix $x_0 in I$ and choose $s>0$ such that
    $K=[x_0-s,x_0+s] subs I$. Choose $C,r>0$ as in $(suit.heart)$
    for this interval $K$.
    Fix $q in NN_0$. By $(circle.filled)$,
    $(L^n f)^((q)) -> g^((q))$ uniformly on $K$. The reverse triangle
    inequality gives
    $
      abs(norm((L^n f)^((q)))_K-norm(g^((q)))_K)
      <=norm((L^n f)^((q))-g^((q)))_K -> 0.
    $
    Since $C$ and $r$ are independent of $n$ and $q$, we have
    $
      norm(g^((q)))_K & = lim_(n->oo) norm((L^n f)^((q)))_K \
                      & <= lim_(n->oo) C q! r^(-q) quad "(by" (suit.heart)")" \
                      & = C q! r^(-q).
    $
    Since $q in NN_0$ was arbitrary, this bound holds for every derivative order.
    Fix $x$ with $abs(x-x_0)<min{s,r}$. Since $g$ is smooth,
    Taylor's theorem and the bound with $q=N+1$ give, for every $N in NN_0$,
    $
      abs(g(x)-sum_(q=0)^N frac(g^((q)) (x_0), q!)(x-x_0)^q) & <= frac(norm(g^((N+1)))_K, (N+1)!) abs(x-x_0)^(N+1) \
                                                             & <= frac(C (N+1)! r^(-(N+1)), (N+1)!) abs(x-x_0)^(N+1) \
                                                             & = C lr((frac(abs(x-x_0), r)))^(N+1).
    $
    Since $abs(x-x_0)/r<1$, the right side tends to zero as $N -> oo$.
    Therefore,
    $
      g(x)=sum_(q=0)^oo frac(g^((q)) (x_0), q!)(x-x_0)^q
      quad "whenever" abs(x-x_0)<min{s,r}.
    $
    Thus $g$ equals its Taylor series on a neighborhood of $x_0$,
    so it is real analytic at $x_0$. Since $x_0 in I$ was arbitrary,
    $g$ is real analytic on $I$, as desired.
    #qed()
  ]
]

#remark[
  For analytic input, @thm:analytic-convergence applies to $D^r$ for every $r in NN$,
  and to $x D$ and $x^2 D$, including on intervals containing zero.
  It gives the corresponding fixed-point equations
  $g^((r))=g$, $x g'=g$, and $x^2 g'=g$. Our previous results
  @drp[Section 3] allow smooth input for $x D$ and $x^2 D$.
]

= A singular counterexample

== Construction of the operator

We construct the operator by reversing the change of variable and
integrating factor from the first-order theorem @drp[Section 2].
The construction starts with a sequence satisfying $H_n '=H_(n+1)$.

For $t>0$ and $n in NN_0$, define
$
  H_n (t):=integral_0^1 s^n e^(s t) dif s.
$
Differentiating under the integral gives $H_n '=H_(n+1)$. This is
justified on each compact $t$-interval by continuity and uniform
boundedness of the integrand and its $t$-derivative on the rectangle.
Also,
$
  H_0 (t)=frac(e^t-1, t).
$
Set $p(t)=t e^(-t)$, so that $p(t)H_0 (t)=1-e^(-t)$, and put
$t(x)=frac(1, x^2)$ for $x!=0$. Then
$p(t(x))H_0 (t(x))=1-e^(-frac(1, x^2))$, which extends smoothly
to the origin with value one by @lem:flat.

For $x!=0$,
$
  frac(dif t, dif x)=-frac(2, x^3),
  quad -frac(x^3, 2) frac(dif t, dif x)=1.
$
Thus the operator $-frac(x^3, 2)D$ becomes differentiation with respect
to $t$. Multiplication by $p$ introduces an extra term, which we
cancel using $frac(p'(t), p(t))=1/t-1$. This leads to
$
  L h:=-frac(x^3, 2)h'+(1-x^2)h.
$
Both coefficients are polynomials, and the leading coefficient has
exactly one zero, of order three, at the origin.

For $H in C^oo ((0,oo))$, define
$w_H (x)=p(t(x))H(t(x))$ on $RR without {0}$. Writing $t=t(x)$,
the chain rule gives
$
  (L w_H)(x) & =frac(dif, dif t)[p(t)H(t)]+(1-1/t)p(t)H(t) \
             & =p(t)H'(t)+[p'(t)+(1-1/t)p(t)]H(t) \
             & =p(t)H'(t).
$
In particular, $L w_(H_n)=w_(H_(n+1))$ on each half-line.

== Smoothness of the input

#lemma[The flat exponential][
  Define
  $
    eta(x):=cases(e^(-frac(1, x^2)) & quad "if" x!=0, 0 & quad "if" x=0).
  $
  Then $eta in C^oo (RR)$ and $eta^((j)) (0)=0$ for every $j in NN_0$.
]<lem:flat>

#pf[
  First, for every $N in NN_0$,
  $
    abs(x)^(-N) e^(-frac(1, x^2)) --> 0 quad "as" x --> 0.
  $
  To verify this, put $y=frac(1, x^2)$ and choose $q in NN$ with $q>N/2$.
  Since $e^y>=frac(y^q, q!)$ for $y>0$, we have
  $0<=y^(N/2)e^(-y)<=q! y^(N/2-q) toinf(y) 0$.

  Off zero, repeated differentiation gives
  $eta^((j)) (x)=P_j (1/x)e^(-frac(1, x^2))$ for polynomials $P_j$.
  Indeed, starting with $P_0=1$, the chain and product rules give
  $
    P_(j+1) (y)=-y^2 P_j ' (y)+2y^3 P_j (y).
  $
  Each of these expressions extends continuously by zero at the
  origin, by the preceding decay estimate. Its difference quotient
  at zero is $frac(P_j (1/x), x)e^(-frac(1, x^2))$, which also tends
  to zero. Inductively, each continuous extension is differentiable
  at zero with derivative zero, and its derivative is the next
  continuous extension. This proves smoothness and all the stated
  derivative values.
]

Set $f=1-eta$. Then $f in C^oo (RR)$, $f(0)=1$, and
$f^((j)) (0)=0$ for $j in NN$. Its Taylor series at zero is the
constant one. Since $f(x)<1$ for every $x!=0$, it cannot agree with
that Taylor series on any neighborhood of zero. Thus $f$ is not
real analytic at zero.

== Orbit formula and convergence

#thm[A discontinuous limit with polynomial coefficients][
  On $RR$, define
  $
    L h=-frac(x^3, 2)h'+(1-x^2)h,
    quad f=1-eta,
  $
  where $eta$ is the function in @lem:flat.
  Then every $L^n f$ is smooth, and for every $n in NN_0$,
  $
    (L^n f)(x)=cases(
      frac(1, x^2) integral_0^1 s^n e^(-frac(1-s, x^2)) dif s & quad "if" x!=0,
      1 & quad "if" x=0.
    )
  $
  Moreover, $0<=L^(n+1) f<=L^n f<=1$ on $RR$, and the sequence
  converges pointwise to the discontinuous function
  $
    g(x)=cases(1 & quad "if" x=0, 0 & quad "if" x!=0).
  $
]<thm:counterexample>

#pf[
  Smoothness of $f$ follows from @lem:flat. Since differentiation and
  multiplication by polynomial coefficients preserve smoothness,
  induction shows that every $L^n f$ is smooth on all of $RR$.

  On $RR without {0}$, we have $f=w_(H_0)$ and
  $L w_(H_n)=w_(H_(n+1))$. Induction therefore gives, with
  $t=frac(1, x^2)$,
  $
    (L^n f)(x)=p(t)H_n (t)
    =t integral_0^1 s^n e^(-(1-s)t) dif s.
  $
  Substituting $t=frac(1, x^2)$ gives the asserted formula.

  At the origin, every smooth $h$ satisfies
  $
    (L h)(0)=h(0).
  $
  Since $f(0)=1$, induction gives $(L^n f)(0)=1$ for all $n$.

  For a fixed $x!=0$, the integral formula implies
  $
    0<=(L^n f)(x)<=frac(1, x^2) integral_0^1 s^n dif s
    =frac(1, x^2(n+1)).
  $
  The right side tends to zero as $n$ tends to infinity. Together
  with the value at zero, this proves the pointwise limit.

  Since $0<=s^(n+1)<=s^n$ on $[0,1]$, the same formula shows
  $0<=(L^(n+1) f)(x)<=(L^n f)(x)$ off zero; the inequalities also hold
  at zero. Finally, $f<=1$. Hence the orbit is nonnegative,
  decreasing, and bounded by one everywhere.
]

== Failure of local uniform convergence

The convergence is uniform on every compact set avoiding zero: if
$abs(x)>=delta>0$, the bound in the proof is at most
$frac(1, delta^2(n+1))$. On any interval containing zero in its
interior, however, convergence cannot be uniform. In fact, each $L^n f$
is continuous and equals one at zero, while $g$ is zero at every
nearby nonzero point. Consequently
$
  sup_(0<abs(x)<=epsilon) abs((L^n f)(x)-g(x))=1
  quad (epsilon>0).
$

There is also an explicit failure of uniform derivative bounds.
Integrating the formula for $L^n f$ by parts in $s$, for $n in NN$,
gives
$
  (L^n f)(x)=1-n x^2 (L^(n-1) f)(x) quad (x!=0).
$
Indeed, the differential of $e^(-(1-s)t)$ is
$t e^(-(1-s)t) dif s$; the boundary term is one and the
remaining integral is $frac(n, t)L^(n-1) f$. By continuity the
recurrence holds at zero as well. Differentiating it twice at zero
therefore gives
$
  (L^n f)^((2)) (0)=-2n (L^(n-1) f)(0)=-2n.
$
Consequently, the local bound on second derivatives required in
@lem:convergence fails at the origin.

For this same operator, @thm:analytic-convergence guarantees an
analytic fixed-point limit whenever an analytic input has a pointwise
convergent orbit. The failure here occurs for the smooth input
$f=1-eta$, whose nonanalyticity at zero was established above.

#block(breakable: false)[
  == The positive-order assumption

  Positive order is also necessary. On $I=(-1,1)$, let
  $
    L h=(1-x^2)h, quad f=1.
  $
  Both the coefficient and the input are real analytic, but
  $
    (L^n f)(x)=(1-x^2)^n --> cases(1 & quad "if" x=0, 0 & quad "if" x!=0).
  $
  Indeed, $0<1-x^2<1$ whenever $0<abs(x)<1$, whereas the value at
  zero is always one. Thus @thm:analytic-convergence does not extend
  to operators of order zero.
]

#block(breakable: false)[
  #bibliography("analytic-iterates.bib", title: "References", style: "chicago-author-date")
]
