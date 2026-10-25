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
local uniform bounds on every derivative; pointwise convergence
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
by the same symbols as the original functions. Write $NN_0={0,1,2,dots}$,
$D=frac(dif, dif x)$, and $h^((0))=h$. For an operator
$
  L h=sum_(j=0)^m a_j h^((j)),
$
write $u_n=L^n f$ for $n in NN_0$, with $u_0=f$. Thus $L u_n=u_(n+1)$.

For a continuous function $h$ on a nonempty compact set $K$, put
$norm(h)_K=sup_(x in K) abs(h(x))$. We say that $v_n$ converges to $g$
*locally uniformly with all derivatives* if $g$ is smooth and
$
  norm(v_n^((q))-g^((q)))_K --> 0
  quad "for every" q in NN_0 "and every compact interval" K subs I.
$
We write $v_n -> g$ in $C^oo_("loc") (I)$ for this convergence.
In the complex plane, $B(z,R)={w in CC st abs(w-z)<R}$ denotes an
open disk, and $overline(B(z,R))$ its closure.

= Elementary estimates

== Interpolation

#lemma[Scaled interpolation][
  Fix an integer $m>=1$. There is a constant $C_m$, depending only
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
  Assume that for every compact interval $J subs I$ and every $j>=0$
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
$L u_n=u_(n+1)$ expresses $u_n^((m))$ in terms of $u_(n+1)$ and the
lower derivatives of $u_n$. The following lemma propagates a bound
for these functions from the center of a disk to a smaller disk.
The smaller radius depends only on the coefficients and the original
radius, so it can be used uniformly along a fixed path.

#lemma[Uniform propagation][
  Fix an integer $m>=1$, a radius $R>0$, and $z_* in CC$. Suppose that
  $c,b_0,dots,b_(m-1)$ and the functions $v_(n,j)$,
  $n in NN_0$, $0<=j<m$, are holomorphic on a common neighborhood
  of $overline(B(z_*,R))$ and satisfy
  $
      v_(n,j) ' & = v_(n,j+1) quad (0<=j<m-1), \
    v_(n,m-1) ' & = c v_(n+1,0)+sum_(j=0)^(m-1)b_j v_(n,j).
  $
  Put $E=overline(B(z_*,R))$. Choose
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
    v_(n,j) (z) & =sum_(k=0)^oo d_(n,j,k)(z-z_*)^k, \
           c(z) & =sum_(ell=0)^oo c_ell (z-z_*)^ell,
                  quad b_j (z)=sum_(ell=0)^oo b_(j,ell)(z-z_*)^ell.
  $
  Cauchy's estimates give
  $
    abs(c_ell)+sum_(j=0)^(m-1)abs(b_(j,ell))<=C_0 R^(-ell).
  $
  Set $T_k=sup_(n>=0,0<=j<m)abs(d_(n,j,k))$, initially allowing
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

  We claim that $T_k<=M A^k$ for all $k>=0$. It holds at $k=0$.
  Assuming it through degree $k$ and using $R A>=2$, we get
  $
    (k+1)T_(k+1) & <=C_0 M A^k sum_(ell=0)^k (R A)^(-ell) \
                 & <=2C_0 M A^k<=M A^(k+1).
  $
  Since $k+1>=1$, this proves the induction step.
  The Taylor series of every $v_(n,j)$ represents it on $B(z_*,R)$,
  and $frac(1, 2A)<=R/4$. Hence, for $abs(z-z_*)<=frac(1, 2A)$,
  $
    abs(v_(n,j) (z))
    <=sum_(k=0)^oo M A^k abs(z-z_*)^k<=2M.
  $
]

== The main theorem

#thm[Analytic input with zeros of the leading coefficient][
  Let $m>=1$ be an integer, let $a_0,dots,a_m$ be real analytic on $I$,
  and suppose $a_m$ is not identically zero. Define
  $
    L h=sum_(j=0)^m a_j h^((j)).
  $
  Let $f$ be real analytic on $I$, and put $u_n=L^n f$.

  If $(u_n (x))_(n>=0)$ is bounded for every $x in I$, then for
  every compact interval $K subs I$ and every $q in NN_0$,
  $
    sup_(n>=0) norm(u_n^((q)))_K<oo.
  $
  If $u_n (x)->g(x)$ for every $x in I$, then $g$ is real analytic,
  $
    L g=g,
    quad u_n --> g "in" C^oo_("loc") (I).
  $
]<thm:analytic-convergence>

#pf[
  *Bounds on one real interval.* First assume pointwise boundedness.
  Since $a_m$ is not identically zero, there is a compact interval
  $J_0=[alpha_0,beta_0] subs I$, with $alpha_0<beta_0$, on which
  $a_m$ does not vanish. For each positive integer $N$, set
  $
    E_N={x in J_0 st abs(u_n (x))<=N "for every" n>=0}.
  $
  These sets are closed and cover $J_0$. Baire's theorem gives an
  $E_N$ with nonempty relative interior. Choose a compact interval
  $J=[alpha,beta] subs E_N$ with $alpha<beta$. Thus
  $norm(u_n)_J<=N$ for all $n$.

  On $J$, set $c=1/a_m$ and $b_j=-frac(a_j, a_m)$ for $0<=j<m$.
  The orbit relation becomes
  $
    u_n^((m))=c u_(n+1)+sum_(j=0)^(m-1)b_j u_n^((j)).
  $
  Write $H_(n,j)=norm(u_n^((j)))_J$. Applying @lem:interpolation
  to each $u_n$, for $0<delta<=frac(beta-alpha, 2m)$, yields
  $
    H_(n,m) & <=norm(c)_J N
              +C_m N sum_(j=0)^(m-1)norm(b_j)_J delta^(-j) \
            & quad +C_m H_(n,m)sum_(j=0)^(m-1)norm(b_j)_J delta^(m-j).
  $
  All powers $m-j$ in the last sum are positive. Choose a fixed
  $delta>0$ small enough that the coefficient of $H_(n,m)$ on the
  right is at most $1/2$. Each $H_(n,m)$ is finite, so moving that
  term to the left gives
  $
    H_(n,m)<=2norm(c)_J N
    +2C_m N sum_(j=0)^(m-1)norm(b_j)_J delta^(-j).
  $
  This bound is independent of $n$. Interpolation now bounds every
  $H_(n,j)$ for $j<m$, uniformly in $n$. In particular, at a chosen
  $x_* in (alpha,beta)$,
  $
    sup_(n>=0,0<=j<m)abs(u_n^((j)) (x_*))<=M_*
  $
  for some finite $M_*$.

  *A common holomorphic domain.* The functions $f,a_0,dots,a_m$
  have holomorphic extensions on a common disk centered at each
  point of $I$. Choose these disks with real diameters contained
  in $I$, and let $Omega$ be their union. If two disks intersect,
  their intersection contains a real interval. The extensions agree
  on that interval, hence on the intersection by the identity
  theorem. They therefore define holomorphic functions on $Omega$.
  The set $Omega$ is connected, since each disk meets $I$.

  Differentiation and multiplication preserve holomorphy on $Omega$,
  so all iterates $u_n=L^n f$ are holomorphic on this same domain.
  The zero set
  $
    Z={z in Omega st a_m (z)=0}
  $
  has no accumulation point in $Omega$, because $a_m$ is holomorphic
  and not identically zero. It is also closed in $Omega$. The functions
  $c=1/a_m$ and $b_j=-frac(a_j, a_m)$ are holomorphic on
  $Omega without Z$.

  *Propagation along paths.* The domain $Omega without Z$ is path
  connected. Indeed, two points can be joined by a polygonal path
  in $Omega$. Its compact image meets only finitely many zeros,
  and small detours around those zeros give a path in $Omega without Z$.

  Fix $z in Omega without Z$ and a continuous path from $x_*$ to
  $z$ in this domain. Its image $Gamma$ is compact. Choose $R>0$
  small enough that the compact set
  $
    E=union.big_(w in Gamma)overline(B(w,R))
  $
  is contained in $Omega without Z$. The coefficients
  $c,b_0,dots,b_(m-1)$ are bounded on $E$. Set
  $
    C_0=max{1,norm(c)_E+sum_(j=0)^(m-1)norm(b_j)_E},
    quad A=max{2/R,2C_0}.
  $
  These choices satisfy @lem:propagation on every disk of radius
  $R$ centered on the path.

  Apply that lemma with $v_(n,j)=u_n^((j))$, $0<=j<m$.
  Uniform continuity of the path allows a finite subdivision whose
  consecutive centers have distance less than $frac(1, 2A)$.
  Starting with the bound $M_*$ at $x_*$, each application gives
  a bound on the next disk at most twice the preceding bound.
  After finitely many steps, all the $u_n$ are uniformly bounded
  on a neighborhood of $z$. Thus the family $(u_n)$ is locally
  bounded on $Omega without Z$.

  *Bounds across a zero.* Fix $z_0 in Z$. Choose $rho>0$ such that
  $overline(B(z_0,rho)) subs Omega$ and this disk contains no other
  zero. Its boundary circle is a compact subset of $Omega without Z$.
  A finite cover by neighborhoods with uniform orbit bounds gives
  a constant $C$ such that
  $
    abs(u_n (z))<=C
    quad (n>=0, abs(z-z_0)=rho).
  $
  Every $u_n$ is holomorphic on a neighborhood of the closed disk,
  including at $z_0$. The maximum-modulus principle gives
  $
    abs(u_n (z))<=C
    quad (n>=0, abs(z-z_0)<=rho).
  $
  Consequently, $(u_n)$ is locally bounded on all of $Omega$.

  *Bounds on derivatives.* Let $K subs I$ be a compact interval.
  Choose $r>0$ so that its closed complex $r$-neighborhood is
  contained in $Omega$. Local boundedness and a finite cover give
  a constant $C_K$ bounding every $u_n$ on this compact neighborhood.
  Cauchy's estimates on disks of radius $r$ centered at $x in K$ give
  $
    norm(u_n^((q)))_K<=C_K q! r^(-q)
    quad (n,q in NN_0).
  $
  This proves the first assertion.

  *Convergence and analyticity of the limit.* Suppose now that
  $u_n (x)->g(x)$ for every $x in I$. Each pointwise orbit is bounded,
  so the preceding estimates apply. By @lem:convergence, $g$ is smooth
  and $u_n -> g$ locally uniformly with all derivatives. Hence we
  can pass to the limit in
  $
    sum_(j=0)^m a_j u_n^((j))=u_(n+1)
  $
  to obtain $L g=g$ throughout $I$, including at zeros of $a_m$.

  Fix $x_0 in I$ and choose $r>0$ such that
  $[x_0-r,x_0+r] subs I$ and $overline(B(x_0,2r)) subs Omega$.
  Let $C$ bound all the $u_n$ on this closed disk. For every real
  $x$ with $abs(x-x_0)<=r$, Cauchy's estimates on $B(x,r)$ and
  convergence of derivatives give
  $
    abs(g^((q)) (x))<=C q! r^(-q) quad (q>=0).
  $
  Taylor's theorem therefore bounds the remainder at $x_0$ by
  $
    abs(g(x)-sum_(q=0)^N frac(g^((q)) (x_0), q!)(x-x_0)^q)
    <=C lr((frac(abs(x-x_0), r)))^(N+1).
  $
  For $abs(x-x_0)<r$ this tends to zero as $N$ tends to infinity.
  Thus $g$ is real analytic at every $x_0 in I$.
]

For analytic input, the theorem applies to $D^r$ for every integer $r>=1$,
and to $x D$ and $x^2 D$, including on intervals containing zero.
It gives the corresponding fixed-point equations
$g^((r))=g$, $x g'=g$, and $x^2 g'=g$. Our previous results
@drp[Section 3] allow smooth input for $x D$ and $x^2 D$.

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
  Then $eta in C^oo (RR)$ and $eta^((j)) (0)=0$ for every $j>=0$.
]<lem:flat>

#pf[
  First, for every integer $N>=0$,
  $
    abs(x)^(-N) e^(-frac(1, x^2)) --> 0 quad "as" x --> 0.
  $
  To verify this, put $y=frac(1, x^2)$ and choose an integer $q>N/2$.
  Since $e^y>=frac(y^q, q!)$ for $y>0$, we have
  $0<=y^(N/2)e^(-y)<=q! y^(N/2-q) ->0$.

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
$f^((j)) (0)=0$ for $j>=1$. Its Taylor series at zero is the
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
  where $eta$ is the function in @lem:flat. Write $u_n=L^n f$.
  Then every $u_n$ is smooth, and for every $n in NN_0$,
  $
    u_n (x)=cases(
      frac(1, x^2) integral_0^1 s^n e^(-frac(1-s, x^2)) dif s & quad "if" x!=0,
      1 & quad "if" x=0.
    )
  $
  Moreover, $0<=u_(n+1)<=u_n<=1$ on $RR$, and the sequence
  converges pointwise to the discontinuous function
  $
    g(x)=cases(1 & quad "if" x=0, 0 & quad "if" x!=0).
  $
]<thm:counterexample>

#pf[
  Smoothness of $f$ follows from @lem:flat. Since differentiation and
  multiplication by polynomial coefficients preserve smoothness,
  induction shows that every $u_n$ is smooth on all of $RR$.

  On $RR without {0}$, we have $f=w_(H_0)$ and
  $L w_(H_n)=w_(H_(n+1))$. Induction therefore gives, with
  $t=frac(1, x^2)$,
  $
    u_n (x)=p(t)H_n (t)
    =t integral_0^1 s^n e^(-(1-s)t) dif s.
  $
  Substituting $t=frac(1, x^2)$ gives the asserted formula.

  At the origin, every smooth $h$ satisfies
  $
    (L h)(0)=h(0).
  $
  Since $f(0)=1$, induction gives $u_n (0)=1$ for all $n$.

  For a fixed $x!=0$, the integral formula implies
  $
    0<=u_n (x)<=frac(1, x^2) integral_0^1 s^n dif s
    =frac(1, x^2(n+1)).
  $
  The right side tends to zero as $n$ tends to infinity. Together
  with the value at zero, this proves the pointwise limit.

  Since $0<=s^(n+1)<=s^n$ on $[0,1]$, the same formula shows
  $0<=u_(n+1) (x)<=u_n (x)$ off zero; the inequalities also hold
  at zero. Finally, $u_0=f<=1$. Hence the orbit is nonnegative,
  decreasing, and bounded by one everywhere.
]

== Failure of local uniform convergence

The convergence is uniform on every compact set avoiding zero: if
$abs(x)>=delta>0$, the bound in the proof is at most
$frac(1, delta^2(n+1))$. On any interval containing zero in its
interior, however, convergence cannot be uniform. In fact, each $u_n$
is continuous and equals one at zero, while $g$ is zero at every
nearby nonzero point. Consequently
$
  sup_(0<abs(x)<=epsilon) abs(u_n (x)-g(x))=1
  quad (epsilon>0).
$

There is also an explicit failure of uniform derivative bounds.
Integrating the formula for $u_n$ by parts in $s$, for $n>=1$,
gives
$
  u_n (x)=1-n x^2 u_(n-1) (x) quad (x!=0).
$
Indeed, the differential of $e^(-(1-s)t)$ is
$t e^(-(1-s)t) dif s$; the boundary term is one and the
remaining integral is $frac(n, t)u_(n-1)$. By continuity the
recurrence holds at zero as well. Differentiating it twice at zero
therefore gives
$
  u_n ''(0)=-2n u_(n-1) (0)=-2n.
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
    L^n f(x)=(1-x^2)^n --> cases(1 & quad "if" x=0, 0 & quad "if" x!=0).
  $
  Indeed, $0<1-x^2<1$ whenever $0<abs(x)<1$, whereas the value at
  zero is always one. Thus @thm:analytic-convergence does not extend
  to operators of order zero.
]

#block(breakable: false)[
  #bibliography("analytic-iterates.bib", title: "References", style: "chicago-author-date")
]
