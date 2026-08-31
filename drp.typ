#import "drp-style.typ": *

#show: preamble
#show: setup-shared-counters(2)
#show: project-header

#set document(
  title: "Iteration of Linear Differential Operators",
  author: ("Jake Edmonstone", "Matthew Tchouikine"),
)

#notes-title("Iteration of Linear Differential Operators")
#align(center)[
  #strong[Jake Edmonstone and Matthew Tchouikine] \
  Mentor: Paul Cusson \
  University of Waterloo Directed Research Program
]

#v(1em)
#outline()
#pagebreak()

= Ordinary differentiation

== The original problem

#problem[Iteration of the derivative][
  Let $d = dif / (dif x)$, and let $f in C^oo (RR)$. Suppose that, for every
  $x in RR$, the limit
  $
    g(x) := lim_(n -> oo) d^n f(x)
  $
  exists. We want to show that $g$ is differentiable and, in fact, satisfies
  $g'=g$.
]

== Analyticity from pointwise derivative bounds

#thm[Analyticity theorem][
  Let $f in C^oo (RR)$. Define
  $
    M(x):=sup{abs(f^((k))(x)) st k>=0},
  $
  and assume that $M(x)<oo$ for every $x in RR$. Then $f$ is the restriction
  to $RR$ of an entire function.
]<thm:analyticity>

#pf[
  Suppose this is not the case. Let $X$ denote the set of real numbers $x$ for which there does not exist any entire function that agrees with $f$ on a neighbourhood of $x$. If $X=em$, then every point has a neighbourhood on which $f$ agrees with some entire function. These entire functions agree on overlaps by analytic continuation, and hence glue to a single entire function agreeing with $f$ on all of $RR$, contradicting our assumption. Therefore $X$ is non-empty. \

  #claim[1][
    The set $X$ is closed.
  ]
  #verifclaim[1][
    Let $(x_n) subs X$. Suppose $x_n -> x nin X$. Then there exists a
    neighbourhood $U subs RR$ of $x$ and an entire function agreeing with
    $f$ on $U$. Since $x_n->x$, we have $x_N in U$ for some $N in NN$. Thus $U$
    is a neighbourhood of $x_N$ on which an entire function agrees with $f$,
    contradicting $x_N in X$. Therefore $x in X$, so $X$ is closed.
  ]

  Now define $S_n:={x in RR st M(x) <= n}$. Then,
  $
    S_n & = {x in RR st f^((k)) (x) in [-n, n] space forall k >= 0} \
        & = inter.big_(k >= 0) ((dif^k f)/(dif x^k))^(-1) ([-n,n])
  $
  Hence each $S_n$ is closed. Also note that
  $ RR = union.big_(n in NN) S_n $
  So
  $
    X = union.big_(n in NN) (S_n inter X)
  $
  Since $X$ is closed in $RR$, it is complete in the induced metric. Since $X$ is also non-empty, BCT implies that there exists an $N in NN$ with $S_N inter X$ having non-empty interior relative to $X$. In other words, there exist $a,b in RR$ with $a < b$ such that
  $
    em != (a,b) inter X subs S_N inter X
  $

  If $(a,b) \\ X=em$, then $(a,b) subs X subs S_N$. Hence
  $
    abs(f^((m))(x)) <= N
  $
  for all $x in (a,b)$ and all $m >= 0$. The Taylor argument below then shows that every $x_0 in (a,b)$ has a neighbourhood on which $f$ agrees with an entire function, contradicting $(a,b) subs X$. Thus $(a,b) \\ X$ is non-empty.

  Now let $(c,e)$ be a maximal interval in the open set $(a,b) \\ X$. Since $(c,e) subs (a,b) \\ X$, for every $x in (c,e)$ there is some neighbourhood of $x$ on which $f$ agrees with an entire function. By analytic continuation, these entire functions agree on overlaps, and hence $f$ agrees with a single entire function $F$ on all of $(c,e)$.

  #claim[2][
    At least one endpoint of $(c,e)$ lies in $(a,b) inter X$.
  ]
  #verifclaim[2][
    Suppose first that $c in (a,b)$. If $c nin X$, then
    $c in (a,b) without X$. Since $(a,b) without X$ is open, some neighbourhood
    of $c$ is contained in $(a,b) without X$. This would extend $(c,e)$ to the
    left, contradicting maximality. Hence, if $c in (a,b)$, then $c in X$.
    Similarly, if $e in (a,b)$, then $e in X$.

    If neither endpoint lies in $(a,b)$, then $(c,e)=(a,b)$, contradicting
    $(a,b) inter X != em$. Therefore at least one endpoint lies in
    $(a,b) inter X$.
  ]

  The argument below treats the case $c in (a,b) inter X$. If instead $e in (a,b) inter X$, the same argument works with $e$ in place of $c$, expanding around $e$ and using $x -> c^+$ at the end. Since $(a,b) inter X subs S_N$, we have $c in S_N$, and so
  $
    abs(f^((m))(c)) <= N
  $
  for all $m >= 0$.

  Since $F|_((c,e))=f|_((c,e))$ and both functions are $C^oo$ there, we have $F^((r))|_((c,e))=f^((r))|_((c,e))$ for every $r >= 0$. Therefore, using continuity of $F^((r))$ and $f^((r))$,
  $
    F^((r))(c) = lim_(x -> c^+) F^((r))(x) = lim_(x -> c^+) f^((r))(x) = f^((r))(c)
  $

  Now let $x in (c,e)$. Since $F$ is entire, Taylor expansion of $F^((m))$ around $c$ gives, for each $m >= 0$,
  $
    f^((m))(x) = F^((m))(x) = sum_(j=0)^oo (F^((m+j))(c))/(j!) (x-c)^j = sum_(j=0)^oo (f^((m+j))(c))/(j!) (x-c)^j
  $
  Thus,
  $
    abs(f^((m))(x)) & <= sum_(j=0)^oo abs(f^((m+j))(c))/(j!) abs(x-c)^j \
                    & <= sum_(j=0)^oo N/(j!) abs(x-c)^j \
                    & <= sum_(j=0)^oo N/(j!) (b-a)^j \
                    & = N exp(b-a)
  $
  for all $m >= 0$ and all $x in (c,e)$. Since $f in C^oo (RR)$, each $f^((m))$ is continuous, so letting $x -> e^-$ gives
  $
    abs(f^((m))(e)) <= N exp(b-a)
  $
  for all $m >= 0$. Hence the bound holds for all $m >= 0$ and all $x in [c,e]$.

  Now let $(c,e)$ vary over all maximal intervals in $(a,b) \\ X$. If $x in (a,b) \\ X$, then $x$ lies in one such interval, and the above argument gives
  $
    abs(f^((m))(x)) <= N exp(b-a)
  $
  for all $m >= 0$. On the other hand, if $x in (a,b) inter X$, then $x in S_N$, and so
  $
    abs(f^((m))(x)) <= N <= N exp(b-a)
  $
  for all $m >= 0$. Hence
  $
    abs(f^((m))(x)) <= N exp(b-a)
  $
  for all $x in (a,b)$ and all $m >= 0$.

  We now show that $f$ is real analytic on $(a,b)$. Let $x_0 in (a,b)$, and choose $r > 0$ such that $(x_0-r,x_0+r) subs (a,b)$. For $x in (x_0-r,x_0+r)$ and $K >= 0$, Taylor's theorem with remainder gives
  $
    f(x) = sum_(j=0)^K (f^((j))(x_0))/(j!) (x-x_0)^j + (f^((K+1))(xi))/((K+1)!) (x-x_0)^(K+1)
  $
  for some $xi$ between $x$ and $x_0$. Therefore,
  $
    abs(f(x) - sum_(j=0)^K (f^((j))(x_0))/(j!) (x-x_0)^j) & <= (N exp(b-a))/((K+1)!) abs(x-x_0)^(K+1)
  $
  Letting $K -> oo$, the right hand side goes to $0$. Hence $f$ agrees with its Taylor series on $(x_0-r,x_0+r)$. Since $x_0 in (a,b)$ was arbitrary, $f$ is real analytic on $(a,b)$.

  Moreover, the same bound shows that this Taylor series has infinite radius of convergence. Indeed, for every $z in CC$,
  $
    sum_(j=0)^oo abs((f^((j))(x_0))/(j!) (z-x_0)^j)
    <= sum_(j=0)^oo (N exp(b-a))/(j!) abs(z-x_0)^j
    = N exp(b-a) exp(abs(z-x_0)) < oo
  $
  Thus the Taylor series at $x_0$ defines an entire function which agrees with $f$ on a neighbourhood of $x_0$. Hence $x_0 nin X$. Since $x_0 in (a,b)$ was arbitrary, $(a,b) inter X = em$. This contradicts $(a,b) inter X != em$.

  Therefore our supposition was false, so $X=em$. Hence every point has a neighbourhood on which $f$ agrees with an entire function. By analytic continuation, these local entire functions agree on overlaps and glue to a single entire function whose restriction to $RR$ is $f$. Therefore $f$ is real analytic with infinite radius of convergence.
]


== Solution of the original problem

#thm[Pointwise limits of iterated derivatives][
  Let $f in C^oo (RR)$ and suppose that
  $
    g(x):=lim_(n->oo) f^((n))(x)
  $
  exists for every $x in RR$. Then $g in C^oo (RR)$ and $g'=g$.
]<thm:ordinary-derivative-limit>

#pf[
  Assume that $f in C^oo (RR)$ and that
  $
    g(x) := lim_(n -> oo) f^((n))(x)
  $
  exists for every $x in RR$. Then for each fixed $x$, the sequence
  $(f^((n))(x))nosp_(n>=0)$ is convergent, hence bounded. Therefore the
  hypotheses of @thm:analyticity are satisfied, so $f$ is the restriction of an
  entire function.

  Indeed, for each $x in RR$, set
  $
    M(x) := sup_(n >= 0) abs(f^((n))(x)).
  $
  This quantity is finite because $(f^((n))(x))nosp_(n>=0)$ converges.

  For all $k>=0$ and $x in RR$ we have
  #stareq(symbol: "1.1")[
    $
      abs(f^((k))(x)) & = abs(sum_(n=0)^oo (f^((n+k))(0))/(n!) x^n) \
                      & <= sum_(n=0)^oo abs(f^((n+k))(0))/(n!) abs(x)^n \
                      & <= sum_(n=0)^oo M(0)/(n!) abs(x)^n \
                      & = M(0) exp(abs(x)).
    $
  ]<eq:global-derivative-bound>

  Let $a<b$. For all $n in NN$ and $x in [a,b]$, we have
  $
    abs(f^((n)) (x))
    <= C_([a,b]) := sup_(x in [a,b]) M(0) exp(abs(x)) < oo.
  $
  For every $n$, the Fundamental Theorem of Calculus gives
  $
    f^((n)) (b) - f^((n)) (a) = integral_a^b f^((n+1)) (x) dif x.
  $
  Taking $n -> oo$ on both sides and applying Lebesgue's Dominated Convergence
  Theorem to the right-hand side gives
  $
        && lim_(n -> oo) (f^((n)) (b)-f^((n)) (a))
          & = lim_(n -> oo) integral_a^b f^((n+1)) (x) dif x \
    ==> && g(b)-g(a)
          & = integral_a^b lim_(n -> oo) f^((n+1)) (x) dif x \
        && & = integral_a^b g(x) dif x.
  $
  Since $g$ is the pointwise limit of the derivatives and
  $abs(f^((n)) (x)) <= C_([a,b])$, we also have
  $abs(g(x)) <= C_([a,b])$ on $[a,b]$. Therefore,
  $
    abs(g(b)-g(a)) & <= integral_a^b abs(g(x)) dif x \
                   & <= C_([a,b]) abs(b-a).
  $
  Thus $g$ is locally Lipschitz, and hence continuous. Fix $b$. The integral
  identity can be written as
  $
    g(x) = g(b) + integral_b^x g(t) dif t.
  $
  Since $g$ is continuous, the Fundamental Theorem of Calculus gives
  $
    g'(x) = g(x).
  $

  Therefore $g'=g$. Since $g$ is continuous, this identity can be differentiated
  inductively to conclude that $g$ is smooth.
]

#lemma[Local form of the ordinary derivative result][
  Let $I subs RR$ be a non-empty open interval and let $F in C^oo (I)$.
  If $lim_(n -> oo) F^((n))(y)$ exists for every $y in I$, then $F$ is the
  restriction to $I$ of an entire function. Moreover, the pointwise limit
  $G$ satisfies $G'=G$ on $I$.
]<lem:local-derivative-limit>

#pf[
  To see this, apply the Baire argument and Taylor estimate from @thm:analyticity on compact subintervals of $I$. Thus every point of $I$ has a neighbourhood on which $F$ agrees with an entire function. These local entire functions agree on overlaps by analytic continuation, and hence glue to a single entire function agreeing with $F$ on all of $I$. The dominated-convergence step is then applied on an arbitrary compact interval $[a,b] subs I$, giving
  $
    G(a)-G(b)=integral_b^a G(x) dif x.
  $
  Since $[a,b]$ was arbitrary, $G'=G$ on all of $I$.
]

= First-order linear differential operators

== The operator $L f=a f'$

#thm[Nowhere-vanishing leading coefficient][
  Let $a in C^oo (RR)$ be nowhere zero, and define the operator
  $
    L f := a f'
  $
  on $C^oo (RR)$. Suppose that for every $x in RR$, the limit
  $
    g(x) := lim_(n -> oo) L^n f(x)
  $
  exists. We want to show that $g$ is differentiable, and in fact satisfies
  $
    L g = g,
  $
  or equivalently,
  $
    a g' = g.
  $
]<thm:af-prime>

#pf[
  Define
  $
    Phi: RR -> RR, quad Phi(x) := integral_0^x 1/(a(t)) dif t.
  $
  Since $a$ is nowhere zero, it has constant sign. Thus $Phi'(x)=1/a(x)$ is nowhere zero, so $Phi$ is a smooth diffeomorphism from $RR$ onto the open interval
  $
    I := Phi(RR) subs RR.
  $
  Let $Phi^(-1): I -> RR$ denote the inverse diffeomorphism. Define
  $
    F := f compose Phi^(-1) : I -> RR.
  $
  Then, for $y in I$, the inverse derivative formula gives
  $
    (Phi^(-1))'(y) = 1/(Phi'(Phi^(-1)(y))) = 1/(1/a(Phi^(-1)(y))) = a(Phi^(-1)(y)).
  $
  Hence, by the chain rule,
  $
    F' & = (f' compose Phi^(-1)) (Phi^(-1))' \
       & = (f' compose Phi^(-1)) (a compose Phi^(-1)) \
       & = (L f) compose Phi^(-1).
  $
  Applying the same computation to $L f$ gives
  $
    F'' & = ((L f)' compose Phi^(-1)) (Phi^(-1))' \
        & = ((L f)' compose Phi^(-1)) (a compose Phi^(-1)) \
        & = (L (L f)) compose Phi^(-1) \
        & = (L^2 f) compose Phi^(-1).
  $
  Applying the same identity inductively gives
  $
    F^((n)) = (L^n f) compose Phi^(-1)
  $
  on $I$ for every $n >= 0$.

  Now define
  $
    G: I -> RR, quad G(y) := lim_(n -> oo) F^((n))(y).
  $
  This limit exists because for every $y in I$, we have $Phi^(-1)(y) in RR$, and so
  $
    G(y) = lim_(n -> oo) (L^n f)(Phi^(-1)(y)) = g(Phi^(-1)(y)).
  $
  Thus
  $
    G = g compose Phi^(-1).
  $
  Now $F in C^oo (I)$, and we have just shown that $lim_(n -> oo) F^((n))(y)$ exists for every $y in I$. The proof of the original problem applies locally on any open interval, so applying it to $F: I -> RR$ gives
  $
    G'=G.
  $
  Since $G=g compose Phi^(-1)$, we also have $g=G compose Phi$. Therefore, for $x in RR$,
  $
    g' & = (G' compose Phi) Phi' \
       & = (G compose Phi) 1/a \
       & = g/a.
  $
  Hence
  $
    a g' = g,
  $
  or equivalently, $L g=g$.
]

== The operator $L f=a f'+f$

#thm[The case $b=1$][
  Let $a in C^oo (RR)$ be nowhere zero, and define the operator
  $
    L f := a f' + f
  $
  on $C^oo (RR)$. Suppose that for every $x in RR$, the limit
  $
    g(x) := lim_(n -> oo) L^n f(x)
  $
  exists. We want to show that $g$ is differentiable, and in fact satisfies
  $
    L g = g
  $
  Moreover, $g$ is constant.
]<thm:af-prime-plus-f>

#pf[
  Define
  $
    Phi: RR -> RR, quad Phi(x) := integral_0^x 1/(a(t)) dif t,
  $
  and let
  $
    I := Phi(RR) subs RR
  $
  As before, $Phi$ is a smooth diffeomorphism from $RR$ onto $I$. Let $Phi^(-1): I -> RR$ denote the inverse diffeomorphism.
  Define
  $
    E: I -> RR, quad E(y) := exp(y)
  $
  Then $E'=E$. Define the function
  $
    F := E (f compose Phi^(-1)) : I -> RR
  $
  Then, using the same calculation as in the first extension,
  $
    F' & = E' (f compose Phi^(-1)) + E ((a f') compose Phi^(-1)) \
       & = E ((f+a f') compose Phi^(-1)) \
       & = E ((L f) compose Phi^(-1))
  $
  Applying the same computation to $L f$ gives
  $
    F'' & = E' ((L f) compose Phi^(-1)) + E ((a (L f)') compose Phi^(-1)) \
        & = E (((L f)+a (L f)') compose Phi^(-1)) \
        & = E ((L (L f)) compose Phi^(-1)) \
        & = E ((L^2 f) compose Phi^(-1))
  $
  Applying the same identity inductively gives
  $
    F^((n)) = E ((L^n f) compose Phi^(-1))
  $
  on $I$ for every $n >= 0$.

  Now define
  $
    G: I -> RR, quad G(y) := lim_(n -> oo) F^((n))(y)
  $
  This limit exists because for every $y in I$,
  $
    G(y) = E(y) lim_(n -> oo) (L^n f)(Phi^(-1)(y)) = E(y) g(Phi^(-1)(y))
  $
  Thus
  $
    G = E (g compose Phi^(-1))
  $
  Now $F in C^oo (I)$, and we have just shown that $lim_(n -> oo) F^((n))(y)$ exists for every $y in I$. The proof of the original problem applies locally on any open interval, so applying it to $F: I -> RR$ gives
  $
    G'=G
  $
  Then
  $
    G' = E' (g compose Phi^(-1)) + E (g compose Phi^(-1))' = E (g compose Phi^(-1)) + E (g compose Phi^(-1))'
  $
  Since $G'=G=E (g compose Phi^(-1))$, we get
  $
    (g compose Phi^(-1))'=0
  $
  Composing with $Phi$ gives
  $
    g'=0
  $
  Hence
  $
    a g' + g = g,
  $
  and therefore $L g=g$.

  It is worth noting that in this case the conclusion is stronger than just $L g=g$: since $a$ is nowhere zero, the equation $a g' + g = g$ forces $g'=0$. Thus convergence under this operator forces the limiting function $g$ to be constant.
]

== The general operator $L f=a f'+b f$

#thm[General nondegenerate first-order operators][
  Let $a,b in C^oo (RR)$, with $a$ nowhere zero, and define the operator
  $
    L f := a f' + b f
  $
  on $C^oo (RR)$. Suppose that for every $x in RR$, the limit
  $
    g(x) := lim_(n -> oo) L^n f(x)
  $
  exists. We want to show that $g$ is differentiable, and in fact satisfies
  $
    L g = g,
  $
  or equivalently,
  $
    a g' + b g = g
  $
]<thm:first-order-nondegenerate>

#pf[
  Define
  $
    Phi: RR -> RR, quad Phi(x) := integral_0^x 1/(a(t)) dif t,
  $
  and let
  $
    I := Phi(RR) subs RR
  $
  As before, $Phi$ is a smooth diffeomorphism from $RR$ onto $I$. Let $Phi^(-1): I -> RR$ denote the inverse diffeomorphism. Since $Phi(0)=0$, we have $0 in I$, so define
  $
    W: I -> RR, quad W(y) := exp(integral_0^y b(Phi^(-1)(s)) dif s)
  $
  Then by the Fundamental Theorem of Calculus,
  $
    W' = W (b compose Phi^(-1))
  $
  Define the function
  $
    F := W (f compose Phi^(-1)) : I -> RR
  $
  Then, using the same calculation as in the first extension,
  $
    F' & = W' (f compose Phi^(-1)) + W ((a f') compose Phi^(-1)) \
       & = W ((b f) compose Phi^(-1)) + W ((a f') compose Phi^(-1)) \
       & = W ((L f) compose Phi^(-1))
  $
  Applying the same computation to $L f$ gives
  $
    F'' & = W' ((L f) compose Phi^(-1)) + W ((a (L f)') compose Phi^(-1)) \
        & = W ((b (L f)) compose Phi^(-1)) + W ((a (L f)') compose Phi^(-1)) \
        & = W ((L (L f)) compose Phi^(-1)) \
        & = W ((L^2 f) compose Phi^(-1))
  $
  Applying the same identity inductively gives
  $
    F^((n)) = W ((L^n f) compose Phi^(-1))
  $
  on $I$ for every $n >= 0$.

  Now define
  $
    G: I -> RR, quad G(y) := lim_(n -> oo) F^((n))(y)
  $
  This limit exists because for every $y in I$,
  $
    G(y) = W(y) lim_(n -> oo) (L^n f)(Phi^(-1)(y)) = W(y) g(Phi^(-1)(y))
  $
  Thus
  $
    G = W (g compose Phi^(-1))
  $
  Now $F in C^oo (I)$, and we have just shown that $lim_(n -> oo) F^((n))(y)$ exists for every $y in I$. The proof of the original problem applies locally on any open interval, so applying it to $F: I -> RR$ gives
  $
    G'=G
  $
  Then
  $
    G' = W' (g compose Phi^(-1)) + W (g compose Phi^(-1))' = W (b compose Phi^(-1)) (g compose Phi^(-1)) + W (g compose Phi^(-1))'
  $
  Since $G'=G=W(g compose Phi^(-1))$, we get
  $
    (g compose Phi^(-1))' + (b compose Phi^(-1)) (g compose Phi^(-1)) = g compose Phi^(-1)
  $
  Now compose this identity with $Phi$. Since $g=(g compose Phi^(-1)) compose Phi$, the chain rule gives
  $
    g' = ((g compose Phi^(-1))' compose Phi) Phi' = ((g compose Phi^(-1))' compose Phi) / a
  $
  Thus
  $
    ((g compose Phi^(-1))' compose Phi) = a g'
  $
  Also, $((b compose Phi^(-1)) compose Phi)=b$ and $((g compose Phi^(-1)) compose Phi)=g$. Therefore composing with $Phi$ gives
  $
    a g' + b g = g
  $
  Therefore $L g=g$.

  This also gives an explicit description of the possible limits. Indeed,
  $
    a g' + b g = g
  $
  is equivalent to
  $
    g' = (1-b)/a g
  $
  Set
  $
    P(x) := integral_0^x frac(1-b(t), a(t)) dif t,
    quad H(x) := g(x) exp(-P(x)).
  $
  By the Fundamental Theorem of Calculus, $P'=(1-b)/a$. Hence the product rule gives
  $
    H' = exp(-P) (g' - P' g) = 0.
  $
  Therefore $H$ is constant, say $H=C$, and thus
  $
    g(x) = C exp(P(x))
         = C exp(integral_0^x frac(1-b(t), a(t)) dif t).
  $
  This recovers the previous cases: if $b=0$, then $g$ is a scalar multiple of $exp(integral (1/a))$, while if $b=1$, then $g$ is constant.
]

= Degenerate leading coefficients

== A simple zero: $L f=x f'$

#thm[Iteration of $x dif/(dif x)$][
  Let $L f:=x f'$ and let $f in C^oo (RR)$. Suppose that
  $
    g(x):=lim_(n->oo) L^n f(x)
  $
  exists for every $x in RR$. Then $f$ is affine. In particular, there are
  $a,b in RR$ such that $f(x)=a+b x$ and $g(x)=b x$, so $g$ is smooth and
  $L g=g$.
]<thm:simple-zero>

#pf[
  This is the simplest example where the coefficient of $f'$ vanishes, so the
  previous change of variables cannot be applied globally. We use the following
  form of the Phragmén--Lindelöf uniqueness theorem.

  #lemma[Phragmén--Lindelöf uniqueness][
    Let $H: CC -> CC$ be entire. Suppose there are constants $C,A>0$ and
    $T in RR$ such that
    $
      abs(H(z)) <= C exp(abs(z))
    $
    for every $z in CC$, and
    $
      abs(H(t)) <= A exp(2t)
    $
    for every real $t<=T$. Then $H=0$.
  ]<lem:pl-uniqueness>

  #pf[
    We reduce this to the standard Phragmén--Lindelöf theorem on the right
    half-plane. Set
    $
      q:=3/2, quad beta:=7/4, quad p(z):=z^q,
    $
    where the principal branch is used on ${z in CC st Re(z)>=0}$, and define
    $
      Q(z):=H(-p(z)) exp(beta p(z)).
    $
    This function is holomorphic on the open right half-plane and continuous
    on its closure. The global bound on $H$ gives
    $
      abs(Q(z)) <= C exp((1+beta) abs(z)^q),
    $
    so $Q$ has growth order $q<2$ there.

    On the imaginary axis,
    $
      Re(p(i y))=-abs(y)^q frac(sqrt(2), 2).
    $
    Since $1-beta frac(sqrt(2), 2)<0$, it follows that $abs(Q(i y))<=C$. On the
    positive real axis, once $-x^q<=T$, the negative-ray bound gives
    $
      abs(Q(x)) <= A exp(-(2-beta)x^q).
    $
    Because $q>1$ and $2-beta>0$, this decays faster than every exponential
    in $x$. The right-half-plane Phragmén--Lindelöf theorem therefore gives
    $Q=0$. Since the complex exponential never vanishes,
    $H(-x^q)=0$ for every $x>0$. These zeros have an accumulation point in
    $CC$, so the identity theorem gives $H=0$.
  ]

  The proof has three steps: conjugate $L$ to the ordinary derivative on each
  half-line, control the growth of the resulting entire functions, and use their
  behaviour near $0$ to force them to be affine-exponential.

  Fix $sigma in {-1,1}$ and define
  $
    I_sigma := cases(
      (0,oo) & "if" sigma=1,
      (-oo,0) & "if" sigma=-1,
    )
  $
  and
  $
    Phi_sigma: I_sigma --> RR, quad Phi_sigma (x) := log(sigma x).
  $
  Then $Phi_sigma$ is a smooth diffeomorphism with inverse
  $
    Phi_sigma^(-1): RR --> I_sigma, quad Phi_sigma^(-1) (y)=sigma exp(y).
  $
  Define
  $
    F_sigma := f compose Phi_sigma^(-1): RR --> RR.
  $
  #claim[1][
    For every $n>=0$,
    $
      F_sigma^((n)) = (L^n f) compose Phi_sigma^(-1).
    $
  ]
  #verifclaim[1][
    Since
    $
      (Phi_sigma^(-1))'=Phi_sigma^(-1),
    $
    the chain rule gives
    $
      F_sigma ' & = (f' compose Phi_sigma^(-1)) (Phi_sigma^(-1))' \
                & = (f' compose Phi_sigma^(-1)) Phi_sigma^(-1) \
                & = (L f) compose Phi_sigma^(-1).
    $
    Applying the same computation to $L f$ gives
    $
      F_sigma '' & = ((L f)' compose Phi_sigma^(-1)) (Phi_sigma^(-1))' \
                 & = ((L f)' compose Phi_sigma^(-1)) Phi_sigma^(-1) \
                 & = (L^2 f) compose Phi_sigma^(-1).
    $
    Applying the identity inductively,
    $
      F_sigma^((n)) = (L^n f) compose Phi_sigma^(-1)
    $
    for every $n>=0$.
  ]

  By Claim 1, @thm:ordinary-derivative-limit applies to $F_sigma$, so $F_sigma$ is the restriction of an entire function, which we continue to denote by $F_sigma$. Set
  $
    a:=f(0), quad b:=f'(0),
  $
  and define the entire function
  $
    H_sigma (z) := F_sigma (z)-a-sigma b exp(z).
  $

  #claim[2][
    There is a constant $C_sigma>0$ such that
    $
      abs(H_sigma (z)) <= C_sigma exp(abs(z))
    $
    for every $z in CC$.
  ]
  #verifclaim[2][
    Since $Phi_sigma^(-1) (0)=sigma$, we have
    $
      F_sigma^((n)) (0) = (L^n f)(sigma).
    $
    Thus the sequence $(F_sigma^((n)) (0))nosp_(n=0)^oo$ converges and is
    therefore bounded. Choose $M_sigma>0$ such that
    $
      abs(F_sigma^((n)) (0)) <= M_sigma
    $
    for every $n>=0$. The Taylor series of $F_sigma$ at $0$ then gives, for every $z in CC$,
    $
      abs(F_sigma (z))
      <= sum_(n=0)^oo frac(M_sigma, n!) abs(z)^n
      = M_sigma exp(abs(z)).
    $
    Since $abs(exp(z))<=exp(abs(z))$, it follows that
    $
      abs(H_sigma (z))
      <= (M_sigma+abs(a)+abs(b)) exp(abs(z)).
    $
    Thus we may take $C_sigma=M_sigma+abs(a)+abs(b)$.
  ]

  #claim[3][
    There are constants $K>0$ and $Y in RR$ such that
    $
      abs(H_sigma (y)) <= K exp(2y)
    $
    for every real $y<=Y$.
  ]
  #verifclaim[3][
    By Taylor's theorem, there are constants $delta,K>0$ such that
    $
      abs(f(x)-a-b x) <= K x^2
    $
    whenever $abs(x)<delta$. Choose $Y in RR$ such that $exp(Y)<delta$. If $y<=Y$, then
    $
      abs(Phi_sigma^(-1) (y))=exp(y)<delta,
    $
    and hence
    $
      abs(F_sigma (y)-a-b Phi_sigma^(-1) (y))
      <= K exp(2y).
    $
    Since $Phi_sigma^(-1) (y)=sigma exp(y)$, this is exactly
    $
      abs(H_sigma (y)) <= K exp(2y)
    $
    for every real $y<=Y$.
  ]

  Claims 2 and 3 verify the two growth hypotheses of @lem:pl-uniqueness. Therefore $H_sigma=0$, and hence
  $
    F_sigma (y)=a+b Phi_sigma^(-1) (y)
  $
  for every $y in RR$. Composing this identity with $Phi_sigma$ gives
  $
    f(x)=a+b x
  $
  for every $x in I_sigma$.

  Since $sigma in {-1,1}$ was arbitrary, this identity holds on both half-lines. Since $f(0)=a$, we conclude that
  $
    f(x)=a+b x
  $
  for every $x in RR$.

  It follows that
  $
    L f(x)=x f'(x)=b x
  $
  and
  $
    L(b x)=b x.
  $
  Thus $L^n f(x)=b x$ for every $n>=1$, and consequently
  $
    g(x)=b x.
  $
  In particular, $g$ is smooth and satisfies
  $
    L g = g.
  $
]

== A second-order zero: $L f=x^2 f'$

#thm[Iteration of $x^2 dif/(dif x)$][
  Let $L f:=x^2 f'$ and let $f in C^oo (RR)$. Suppose that
  $
    g(x):=lim_(n->oo) L^n f(x)
  $
  exists for every $x in RR$. Then, for some $C in RR$,
  $
    g(x)=cases(
      C exp(-1/x) & x>0,
      0 & x<=0.
    )
  $
  In particular, $g in C^oo (RR)$ and $L g=g$.
]<thm:second-order-zero>

#pf[
  Define
  $
    Phi_+: (0,oo) & --> RR \
                x & mapstoo -1 / x
  $
  Note that $Phi_+$ is self-inverse, so $(Phi_+^(-1))'(x)= Phi_+ '(x)=1/x^2$ for all $x in (0,oo)$. Denote $F_+ = f compose Phi_+^(-1)$.

  #lemma[Conjugacy on the positive half-line][
    For all $n in NN$,
    $
      F_+^((n)) = (L^n f) compose Phi_+^(-1).
    $
  ]<lem:positive-half-line-conjugacy>

  #pf[
    Applying the chain rule, we have
    $
      F_+ ' = (f compose Phi_+^(-1))'
      = (f' compose Phi_+^(-1)) dot (Phi_+^(-1))'.
    $
    Therefore, for $y in (-oo,0)$, we have
    $
      F_+ ' (y) & = f'(Phi_+^(-1) (y)) (Phi_+^(-1))'(y) \
                & = f'(-1/y) (1/y^2) \
                & = f'(Phi_+^(-1) (y)) (Phi_+^(-1) (y))^2 \
                & = (L f)(Phi_+^(-1) (y)).
    $
    So $F_+ '=(L f) compose Phi_+^(-1)$.

    We also have
    $
      F_+^((2)) & = ((L f) compose Phi_+^(-1))' \
                & = ((L f)' compose Phi_+^(-1)) (Phi_+^(-1))' \
    $
    Therefore, for $y in (-oo,0)$, we have
    $
      F_+^((2))(y) & = (L f)'(Phi_+^(-1) (y)) (Phi_+^(-1) (y))^2 \
                   & = (L^2 f)(Phi_+^(-1) (y)).
    $

    So $F_+^((2)) = (L^2 f) compose Phi_+^(-1)$.

    Inductively,
    $
      F_+^((n)) = (L^n f) compose Phi_+^(-1)
    $
    which concludes the proof.
  ]

  Note that $F_+ in C^oo ((-oo,0))$. By
  @lem:positive-half-line-conjugacy and the hypothesis on $L^n f$, the limit
  $lim_(n -> oo) F_+^((n))(y)$ exists for every $y in (-oo,0)$. Thus
  @lem:local-derivative-limit applies directly to $F_+$. If
  $
    G_+(y) := lim_(n -> oo) F_+^((n))(y),
  $
  then $G_+ '=G_+$ on $(-oo,0)$, so
  $
    G_+(y)=C_+ exp(y)
  $
  for some $C_+ in RR$. Note that $G_+=g compose Phi_+^(-1)$, so $g = G_+ compose Phi_+$. Therefore, for $x>0$ we get
  $
    g(x)=C_+ exp(-1/x)
  $

  Now, define
  $
    Phi_-: (-oo,0) & --> RR \
            quad x & mapstoo -1 / x
  $
  and denote $F_- = f compose Phi_-^(-1)$.

  #lemma[Conjugacy on the negative half-line][
    For all $n in NN$,
    $
      F_-^((n)) = (L^n f) compose Phi_-^(-1).
    $
  ]<lem:negative-half-line-conjugacy>

  #pf[
    The proof is analogous to that of @lem:positive-half-line-conjugacy.
  ]

  Analogously, @lem:local-derivative-limit gives
  $
    G_-(y) := lim_(n -> oo) F_-^((n))(y) = C_- exp(y)
  $
  for some $C_- in RR$.

  #lemma[Vanishing on the negative half-line][
    We have $C_-=0$.
  ]<lem:negative-constant-zero>

  #pf[
    First note that $f$ is continuous at $0$ because it is smooth, so
    $
      lim_(y->oo) F_-(y)=lim_(y->oo) f(-1/y)= f(lim_(y->oo) -1/y) = f(0)
    $
    Since $exp(-y)->0$ as $y->oo$, the product rule for limits gives
    $
      lim_(y->oo) exp(-y)F_-(y)=0.
    $

    By @lem:local-derivative-limit, $F_-$ agrees on $(0,oo)$ with the restriction of an entire function $tilde(F)_-$. Therefore, for every $y_0>0$, its Taylor series centered at $y_0$ has infinite radius of convergence. Set
    $
      H(y) := F_-(y) - C_- exp(y)
    $
    on $(0,oo)$. Since entire functions are closed under linear combinations, the function
    $
      tilde(H)(z) := tilde(F)_-(z) - C_- exp(z)
    $
    is entire. Moreover, for every $y in (0,oo)$,
    $
      tilde(H)(y) = F_-(y) - C_- exp(y) = H(y).
    $
    Thus $H$ agrees on $(0,oo)$ with the restriction of the entire function $tilde(H)$. Also, for every $y>0$,
    $
      H^((n))(y)
      = F_-^((n))(y) - C_- exp(y)
      toinf(n) 0
    $
    because $F_-^((n))(y) toinf(n) C_- exp(y)$.

    Fix $y_0>0$, and define
    $
      a_k := H^((k))(y_0).
    $
    For $r>0$, the Taylor expansion at $y_0$ gives
    $
      H(y_0+r)=sum_(k=0)^oo a_k/(k!) r^k
    $
    and hence
    $
      exp(-r) H(y_0+r)
      = sum_(k=0)^oo a_k exp(-r) r^k / k!
    $
    We claim that the right hand side tends to $0$ as $r -> oo$. Let $epsilon>0$. Since $a_k -> 0$, choose $K$ such that $abs(a_k)<epsilon/2$ for every $k>=K$. Then
    #stareq(symbol: "3.1")[
      $
        abs(exp(-r)H(y_0+r)) & <= sum_(k=0)^(K-1) abs(a_k) exp(-r) r^k/(k!) \
                             & quad + epsilon/2 sum_(k=K)^oo exp(-r) r^k/(k!).
      $
    ]<eq:split-exponential-series>
    However,
    $
      sum_(k=0)^(K-1) abs(a_k) exp(-r) r^k/(k!)
      toinf(r) 0
    $
    because $r^k in o(exp(r))$ for any $k in NN$. Note further that
    $
      epsilon/2 sum_(k=K)^oo exp(-r) r^k/(k!)
      <= epsilon/2 exp(-r) exp(r)
      = epsilon/2
    $
    because $r^k/k! >= 0$ for all $r>=0$.

    Combining these estimates with @eq:split-exponential-series, we have
    $
      abs(exp(-r)H(y_0+r))
      <= sum_(k=0)^(K-1) abs(a_k) exp(-r) r^k/(k!) + epsilon/2.
    $
    The finite sum is less than $epsilon/2$ for all sufficiently large $r$. Hence
    $
      abs(exp(-r)H(y_0+r)) < epsilon
    $
    for all sufficiently large $r$. Since $epsilon>0$ was arbitrary,
    $
      lim_(r->oo) exp(-r) H(y_0+r) = 0
    $
    Now let $y=y_0+r$. Then
    $
      exp(-y)H(y) & = exp(-y_0-r)H(y) \
                  & = exp(-y_0) exp(-r)H(y_0+r).
    $
    Since $exp(-y_0)$ is constant and $r->oo$ if and only if $y->oo$, it follows that
    $
      lim_(y->oo) exp(-y)H(y)=0.
    $

    Now,
    $
      exp(-y) F_-(y) & =exp(-y) (C_- exp(y) + H(y)) quad ("by definition of" H) \
                     & = C_- + exp(-y) H(y),
    $
    so
    #stareq(symbol: "3.2")[
      $
        lim_(y->oo) exp(-y) F_-(y) = C_-.
      $
    ]<eq:negative-limit-constant>
    The direct limit calculation at the start of the proof shows that the same
    limit is $0$. Therefore, by @eq:negative-limit-constant, we have $C_-=0$.
  ]

  #lemma[Smooth gluing lemma][
    Let $h in C^oo ((0,oo))$ and suppose that
    $
      lim_(x->0^+) h^((n))(x)=0
    $
    for every $n>=0$. Then the extension
    $
      tilde(h)(x)=cases(
        h(x) & x>0,
        0 & x<=0
      )
    $
    belongs to $C^oo (RR)$.
  ]<lem:smooth-gluing>

  #pf[
    See #link("https://ems.press/content/serial-article-files/51546")[
      Francis, Lemma 6.2
    ], which proves the more general extension-by-zero principle in $RR^d$.
  ]

  Since $C_-=0$, we have $G_-equiv 0$, yet $G_-=g compose Phi_-^(-1)$ with $Phi_-^(-1)(y)=-1/y != 0$ for any $y in (0,oo)$. Therefore, $g(x)=0$
  for $x<0$. Also, at $x=0$, we have $(L h)(0)=0$ for every smooth function $h$, so $g(0)=0$. Therefore any pointwise limit has the form
  $
    g(x)=
    cases(
      C_+ exp(-1/x)\, & x>0,
      0\, & x<=0
    )
  $
  Note that $g$ is clearly smooth on $RR^*$. On $(-oo,0]$, every derivative of $g$ is zero. For every $n>=0$, the $n$th derivative of the right-hand piece has the form
  $
    P_n (1/x) exp(-1/x)=(P_n (1/x))/exp(1/x)
  $
  for some polynomial $P_n$, which tends to $0$ as $x -> 0^+$ because exponential growth dominates polynomial growth. Thus, by @lem:smooth-gluing, $g$ is smooth at $0$, and therefore $g in C^oo (RR)$, as desired.

  #remark[Why $C_+$ need not vanish][
    The constant $C_+$ need not be zero. On the negative half-line, $x->0^-$ corresponds to $y->oo$, where $F_-$ is bounded and $exp(-y)->0$, forcing $C_-=0$. On the positive half-line, $x->0^+$ corresponds instead to $y->-oo$, where $exp(-y)->oo$, so the same argument fails. Indeed, for any $C in RR$, the smooth function
    $
      f_C (x)=cases(C exp(-1/x)\, & x>0, 0\, & x<=0)
    $
    satisfies $L f_C=f_C$. Hence $L^n f_C=f_C$ for every $n$, showing that any value $C_+=C$ can occur.
  ]
]


= Structural decomposition

== Three important spaces

#defn[Transient, input, and fixed-point spaces][
  Let $L: C^oo (RR) -> C^oo (RR)$ be a linear differential operator, and define
  $
    A := {h in C^oo (RR) st lim_(n -> oo) L^n h(x) = 0 "for every" x in RR}
  $
  This is the transient space. Define
  $
    B := {f in C^oo (RR) st lim_(n -> oo) L^n f(x) "exists for every" x in RR}
  $
  This is the input space. Finally, define
  $
    C := {g in C^oo (RR) st L g = g}
  $
  This is the fixed-point space.
]<defn:three-spaces>

#prop[Transient--fixed-point decomposition][
  Assume that, for every $f in B$, the pointwise limit
  $
    g(x) := lim_(n -> oo) L^n f(x)
  $
  belongs to $C^oo (RR)$ and satisfies $L g = g$. Then
  $
    B = A + C.
  $
]<prop:transient-fixed-point-decomposition>

#pf[
  First let $f in B$, and define
  $
    g(x) := lim_(n -> oo) L^n f(x)
  $
  By the hypothesis, $g in C$. Let
  $
    h := f - g
  $
  Then $h in C^oo (RR)$, and for every $x in RR$,
  $
    L^n h(x)
    = L^n f(x) - L^n g(x)
    = L^n f(x) - g(x)
    -> 0
  $
  Thus $h in A$, and therefore
  $
    f = h + g in A + C
  $
  So $B subs A + C$.

  Conversely, let $f in A + C$. Then there exist $h in A$ and $g in C$ such that
  $
    f = h + g
  $
  Since $L g = g$, we have $L^n g = g$ for every $n >= 0$. Hence, for every $x in RR$,
  $
    L^n f(x)
    = L^n h(x) + L^n g(x)
    = L^n h(x) + g(x)
    -> g(x)
  $
  Therefore the limit $lim_(n -> oo) L^n f(x)$ exists for every $x in RR$, so $f in B$. Hence
  $
    A + C subs B
  $

  Combining the two inclusions gives
  $
    B = A + C
  $
]
