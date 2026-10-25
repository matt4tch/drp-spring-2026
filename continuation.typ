#import "drp-style.typ": *

#show: preamble
#show: setup-shared-counters(2)
#show: project-header

#set document(
  title: "Pointwise Limits of Differential-Operator Iterates: Working Notes",
  author: "Jake Edmonstone",
)

// Keep the original document's layout, with a header for these personal notes.
#set page(header: [
  #smallcaps[Directed Research Program — Continuation]
  #h(1fr)
  #smallcaps[J. Edmonstone]
  #block(spacing: .65em, line(length: 100%, stroke: 1pt))
])

// Replace these prompts with your own statements, explanations, and proofs.
#let to-write(body) = block[
  #emph[To write.] #body
]

#notes-title("Pointwise Limits of Differential-Operator Iterates")
#align(center)[
  #strong[Working notes — Jake Edmonstone] \
  A continuation of _Iteration of Linear Differential Operators_
]

#v(1em)
These notes are a place to reconstruct the continuation in my own words.
The goal is to understand the real scalar case $P=D^2$, building on the
#link("drp.pdf")[original DRP write-up]. Statements below are targets to
prove; the proof drafts are unfinished.

#outline()
#pagebreak()

= From the original problem to second derivatives

== What I already know

For ordinary differentiation, the original project proves that
$f^((n)) (x) -> g(x)$ at every point forces $g$ to be smooth and to satisfy
$g'=g$. Pointwise convergence gives pointwise bounds on all derivatives;
Tao's theorem gives an entire extension, which supplies uniform bounds on
compact intervals. Those bounds justify passing to the limit in the integral
identity.

#to-write[
  Summarize that argument in my own words. Identify exactly where pointwise
  convergence alone would be insufficient, and explain how the coordinate
  change and integrating factor handle $L=a D+b$ when $a$ is nowhere zero.
]

== The first new problem

Throughout the first proof, let $I subs RR$ be a nonempty open interval,
$f in C^oo (I)$ be real valued, and $D=dif/(dif x)$. Write
$NN_0={0,1,2,dots}$ and define
$
  u_n := (D^2)^n f = f^((2n)), quad n in NN_0.
$
The relation linking consecutive iterates is
$
  u_n '' = u_(n+1).
$

#thm[Second-derivative limit — target statement][
  Suppose $u_n (x) -> g(x)$ for every $x in I$. Then $g in C^oo (I)$,
  $g''=g$, and $u_n -> g$ in $C^oo_("loc")(I)$. In particular,
  $
    g(x)=A e^x+B e^(-x)
  $
  for real constants $A,B$.
]<thm:second-derivative-target>

#to-write[
  Restate the theorem without notation for local smooth convergence.
  Explain why knowing the even derivatives are pointwise bounded does not
  immediately let me use the original all-derivatives theorem.
]

== The bounds I need

For a compact interval $K subs I$ and $k>=0$, put
$
  norm(h)_(C^k (K)) := max_(0<=j<=k) sup_(x in K) abs(h^((j)) (x)).
$
Convergence in $C^oo_("loc")(I)$ means that these norms of $u_n-g$ tend to
zero for every such $K$ and $k$.

Pointwise convergence gives
$
  M(x):=sup_(n>=0) abs(u_n (x))<oo quad (x in I).
$
The main task is to obtain
$
  sup_(n>=0) norm(u_n)_(C^k (K))<oo
$
for every $K$ and $k$. First obtain local uniform bounds for the functions;
then use $u_n ''=u_(n+1)$ to control their derivatives.

= Reconstructing the proof for $D^2$

== Two endpoints control a short interval

#lemma[Scalar endpoint estimate][
  Let $c<e$, $ell=e-c$, and $h in C^2 ([c,e])$. Then
  $
    norm(h)_(C^0([c,e]))
    <= max{abs(h(c)),abs(h(e))}
    + frac(ell^2, 8) norm(h'')_(C^0([c,e])).
  $
]<lem:endpoint-estimate>

*Proof draft.* Subtract the affine interpolant
$
  a_h (x):=frac(e-x, ell)h(c)+frac(x-c, ell)h(e).
$
The difference $h-a_h$ vanishes at both endpoints and has second derivative
$h''$.

#to-write[
  Derive the integral representation for this difference. Compute the
  integral of the absolute value of its Green kernel and explain the
  constant $ell^2/8$.
]

== The good set and the first Baire argument

#defn[Good and exceptional points][
  Define
  $
    G := {x in I st M "is bounded on a neighborhood of" x},
    quad F := I without G.
  $
  A point belongs to $G$ when a single bound controls all iterates throughout
  some neighborhood of that point.
]

*Proof draft: $G$ is open and dense.* For each positive integer $m$, set
$
  S_m := {x in I st M(x)<=m}
  = inter.big_(n>=0) {x in I st abs(u_n (x))<=m}.
$

#to-write[
  Prove that each $S_m$ is relatively closed and that these sets cover $I$.
  Apply Baire on a compact interval inside an arbitrary open subinterval
  of $I$ to prove density of $G$. Explain separately why $G$ is open.
]

== Putting the orbit in a sequence space

Let $E=ell^oo (NN_0;RR)$ be the Banach space of bounded real sequences with
the supremum norm. Define the left shift by
$
                    S:E & --> E \
  (xi_0,xi_1,xi_2,dots) & mapstoo (xi_1,xi_2,xi_3,dots).
$
For $x in G$, package all iterates into
$
  U(x):=(u_0(x),u_1(x),u_2(x),dots).
$
The intended equation is $U''=S U$, with $norm(S)=1$ and $norm(U(x))=M(x)$.

#to-write[
  Use local uniform bounds on $u_n$ and $u_n ''$ to bound $u_n '$ on compact
  intervals in $G$, then repeat to bound every derivative. Justify
  differentiating $U$ in the supremum norm. Explain how the equation for
  $(U,U')$ extends its solution to a finite endpoint of a component of $G$,
  and how coordinate evaluation identifies the endpoint values.
]

#remark[Point to check carefully][
  Although $U(x)$ is a bounded sequence at every point of $I$, its
  norm-smoothness has only been established on $G$. Continuing an ODE
  solution beyond a good component does not yet identify it with the
  original orbit there.
]

== Eliminating the exceptional set

*Proof draft: $F$ is empty.* Suppose otherwise. Apply Baire again, now to
the relatively closed set $F$, to obtain a small interval $J$ meeting $F$
and a bound $m$ for $M$ on $F inter J$. Choose
$a<x_0<b$ with $x_0 in F inter J$ and $a,b in G inter J$.

#to-write[
  Make this second Baire argument precise. For each component $(c,e)$ of
  $G inter (a,b)$, explain why the endpoint values are bounded by
  $M_0=max{m,M(a),M(b)}$. Apply @lem:endpoint-estimate to the sequence-valued
  solution, choose $J$ short enough to absorb the term containing
  $ell^2/8$, and obtain a bound on all of $[a,b]$. State the contradiction.
]

== Passing to the limit

#to-write[
  Explain why local uniform derivative bounds and pointwise convergence
  imply uniform convergence on compact intervals. For $w=u_n-u_m$, use
  Taylor's formula and a uniform bound on $w''$ to show that $w'$ tends
  uniformly to zero on a smaller compact interval. Repeat for higher
  derivatives, identify their limits, and pass $u_n ''=u_(n+1)$ to $g''=g$.
  Finish the proof of @thm:second-derivative-target.
]

= Questions to bring to a meeting

#to-write[
  Record the exact statement or proof step I cannot yet justify, what I
  tried, and which hypothesis seems to matter.
]
