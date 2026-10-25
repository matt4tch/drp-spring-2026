# A scalar undergraduate continuation of the DRP

Prepared October 17, 2026. This is a proposal for scope and proof development,
not a claim of publication novelty or a verification of the full AI-assisted
manuscript.

The intended readers know real analysis, Baire category, measure theory, and
complex analysis. They have not taken differential equations or functional
analysis. The goal is understandable proofs first, followed by a focused attempt
at a new result.

## Recommendation

Use the unified manuscript as a collection of possible results, rather than as
the outline of the undergraduate paper. Work with real-valued smooth functions
on an open interval, and first study ordinary differentiation, its square, and
squares of the first-order operators already treated in the original DRP.

The recommended core, updated to include analytic input and a counterexample,
is:

1. Recover the original derivative result, including convergence of all
   derivatives uniformly on compact subintervals.
2. Give a scalar proof for even derivatives using Baire category, Taylor's
   theorem, and an elementary endpoint estimate.
3. Transfer that result to squares of regular real first-order operators using
   the original change of coordinates and integrating factor.
4. Treat arbitrary derivative powers for real-analytic input.
5. Construct and prove the explicit singular first-order counterexample below.

Sampling questions, sign conditions, and further singular classifications are
possible later extensions. They are not prerequisites for finishing this paper.

## An explicit undergraduate counterexample

This example disproves the unrestricted smooth scalar first-order extension.
It does not disprove the ordinary-derivative theorem, and it is not a regular
operator at the origin. It also does not by itself show that the analytic-input
hypothesis is necessary for a regular operator. Those are different questions.

Define, on the whole real line,

\[
Lh=-\frac{x^3}{2}h'+(1-x^2)h,
\qquad
f(x)=\begin{cases}
1-e^{-1/x^2},&x\ne0,\\
1,&x=0.
\end{cases}
\]

The coefficients are polynomials. The leading coefficient vanishes only at
zero, where it has a zero of order three. The input is smooth because the
function equal to \(e^{-1/x^2}\) off zero and zero at zero is smooth and flat.
The input is not real analytic at zero: its Taylor series there is the constant
one.

For every \(n\ge0\), the full orbit satisfies

\[
L^nf(0)=1,
\qquad
L^nf(x)=\frac1{x^2}\int_0^1
 s^n\exp\left(-\frac{1-s}{x^2}\right)\,ds\quad(x\ne0).
\]

Here is a proof using the original integrating-factor idea.
For \(x\ne0\), put \(t=1/x^2\), and write

\[
H_n(t)=\int_0^1 s^n e^{st}\,ds.
\]

Differentiation gives \(H_n'=H_{n+1}\), while

\[
t e^{-t}H_0(t)=1-e^{-t}=f(x).
\]

The chain rule gives \((-x^3/2)(dt/dx)=1\), so direct differentiation shows

\[
L\bigl[t e^{-t}H(t)\bigr]=t e^{-t}H'(t).
\]

Iterating this identity proves the integral formula away from zero. At zero,
\((Lh)(0)=h(0)\) for every smooth \(h\), so induction gives \(L^nf(0)=1\).
All iterates are smooth because \(L\) maps smooth functions to smooth functions.

For any fixed \(x\ne0\),

\[
0\le L^nf(x)
\le\frac1{x^2}\int_0^1s^n\,ds
=\frac1{x^2(n+1)}\longrightarrow0.
\]

Consequently

\[
L^nf\longrightarrow\mathbf1_{\{0\}}
\quad\text{pointwise on }\mathbb R.
\]

This is one fixed input and one fixed differential operator, with convergence
of the entire orbit at every point. The limit is discontinuous. The integral
formula also shows that the orbit is nonnegative and nonincreasing in \(n\),
with \(0\le L^nf\le f\le1\) everywhere. Thus even a uniform absolute bound
and monotonicity do not rescue smoothness in this singular setting.

An alternative exact formula, useful for checking the calculation, is

\[
L^nf(x)=\sum_{k=0}^n(-1)^k\frac{n!}{(n-k)!}x^{2k}
       -(-1)^n n!x^{2n}e^{-1/x^2}\quad(x\ne0).
\]

In particular, for \(n\ge1\), \((L^nf)''(0)=-2n\), so the spatial second
derivatives are not locally uniformly bounded. An exact polynomial recurrence
check for \(n=0,\ldots,12\) corroborated the formula; the chain-rule proof
above establishes it for all \(n\).

The construction starts with an elementary sequence
\(H_n(t)=\int_0^1s^ne^{st}\,ds\), for which differentiation shifts the index
and \(H_n(t)\to0\) at each fixed \(t\). Reversing the familiar coordinate
change and integrating factor makes a smooth input at the singular endpoint,
where the operator preserves its value. This is a tractable way to learn how
to design a counterexample, rather than merely verify a supplied formula.

The polynomial operator and smooth input above were derived and checked during
this discussion. No claim of literature novelty is made. The unified draft
explicitly leaves general zeroth-order terms at degenerate first-order zeros
outside its classification, so this does not contradict its stated positive
theorems.

If a counterexample with a nowhere-vanishing leading coefficient is required,
this example does not meet that requirement. The manuscript's \(D^3\)
construction is the relevant harder target; one should not promise the same
elementary proof length for it.

## What restricting the setting does and does not achieve

Write the domain as a connected open interval \(I\subset\mathbb R\), with
\(f:I\to\mathbb R\). An arbitrary open subset of the real line can be treated
one connected component at a time.

For scalar operators

\[
Pf=\sum_{j=0}^r a_j(x)f^{(j)}(x),
\]

the coefficients are ordinary real smooth functions. Operator-norm smoothness,
operator-valued coefficients, and Fréchet derivatives are unnecessary.

However, this restriction alone does not make the unified manuscript elementary.
Its proof for even scalar functions still packages the iterates in
\(\ell^\infty\) and solves an ODE there. Its higher-order counterexample is
already a smooth function \(\mathbb R\to\mathbb R\). Removing Banach-valued
input does not remove that construction's difficulty. The proof architecture
and the number of topics must also change.

There is a real advantage to scalar values: inequalities, convexity, and Rolle's
theorem provide tools that are unavailable in an unordered Banach space.

## Two elementary estimates replace much of the initial machinery

### Missing first derivatives

Taylor's formula gives, when the segment from \(x\) to \(x+t\) is in the domain,

\[
|h'(x)|\le \frac{2}{|t|}\sup|h|
                +\frac{|t|}{2}\sup|h''|.
\]

On a fixed nontrivial interval, choose a fixed small \(|t|\), with the sign chosen
according to the available space. Thus a common bound for \(h\) and \(h''\)
gives a common bound for \(h'\).

For \(h=f^{(2n)}\), uniform bounds for the even derivatives therefore control
every odd derivative, with a constant independent of \(n\). This is the
mechanism behind passing from bounds on even derivatives to bounds on all
derivatives.

### Endpoint control without a Green function

Let \(h\in C^2([a,b])\), and let \(p\) be its affine endpoint interpolant.
Set \(v=h-p\) and \(B=\sup_{[a,b]}|h''|\). Define

\[
q(x)=\frac B2(x-a)(b-x).
\]

Both \(v-q\) and \(-v-q\) have nonnegative second derivative and zero endpoint
values. A convex function lies below its endpoint chord, so both are
nonpositive. Consequently

\[
|h(x)-p(x)|\le\frac B2(x-a)(b-x)
\]

and hence

\[
\sup_{[a,b]}|h|
\le\max\{|h(a)|,|h(b)|\}
    +\frac{(b-a)^2}{8}\sup_{[a,b]}|h''|.
\]

This is the scalar estimate underlying Lemma 3.2. Its proof requires only
convexity and differentiation of a quadratic. A Green function is an optional
interpretation, not a prerequisite.

## Main theorem: even derivatives

The first substantial target is the following known scalar result.

**Theorem.** Suppose \(f\in C^\infty(I;\mathbb R)\) and

\[
\sup_{n\ge0}|f^{(2n)}(x)|<\infty\qquad(x\in I).
\]

Then all derivatives are locally uniformly bounded simultaneously: for every
compact interval \(K\subset I\),

\[
\sup_{m\ge0}\sup_{x\in K}|f^{(m)}(x)|<\infty.
\]

In particular, \(f\) extends to an entire function. If the even derivatives
converge pointwise, their limit is

\[
g(x)=Ae^x+Be^{-x},
\]

and every spatial derivative of \(f^{(2n)}\) converges uniformly on compact
subintervals to the corresponding derivative of \(g\).

Adams's Theorems 42 and 57 provide a prior scalar boundedness and convergence
result. This belongs in the paper as an attributed theorem with an accessible
proof, not as a newly discovered result.

### A proof route avoiding sequence spaces

Put \(u_n=f^{(2n)}\), so \(u_n''=u_{n+1}\), and define

\[
M(x)=\sup_n|u_n(x)|,
\qquad G=\{x:M\text{ is bounded on a neighborhood of }x\}.
\]

1. Baire category shows that \(G\) is open and dense.
2. On compact intervals in \(G\), the Taylor estimate above bounds all odd
   derivatives as well as the even ones. The bounds are uniform over the
   derivative order.
3. On each connected component of \(G\), Taylor's theorem therefore gives an
   entire extension of \(f\). Local extensions agree and give one entire
   function on that component. This uses the same reasoning as the original
   DRP's analyticity argument.
4. At a finite endpoint of that component inside \(I\), continuity identifies
   every derivative of the extension with the corresponding derivative of the
   original smooth function. The simultaneous derivative bounds at an interior
   point \(x_*\) give, by Taylor expansion,
   \(|F^{(m)}(x)|\le C e^{|x-x_*|}\) for every \(m\). Thus the supremum over
   its even derivatives is finite on any bounded closed interval. An arbitrary
   entire extension, without these coefficient bounds, would not suffice.
5. If \(F=I\setminus G\) is nonempty, apply Baire to \(F\) to obtain a small
   interval on whose intersection with \(F\), \(M\) has a common bound. Bracket
   a point of \(F\) with two points of \(G\).
6. Every intervening good component has bounded endpoint values. The endpoint
   estimate applied to every \(u_n\), followed by a supremum over \(n\), gives
   a bound throughout that component when the surrounding interval is short
   enough. Together with the bound on \(F\), this makes \(M\) bounded in a
   neighborhood of the chosen bad point: a contradiction.
7. Once \(G=I\), the first Taylor estimate controls all derivatives. Elementary
   equicontinuity and Taylor estimates upgrade pointwise convergence to uniform
   convergence of all derivatives on compact subintervals. Thus
   \(u_n''=u_{n+1}\) passes to \(g''=g\).

Step 4 matters: one must establish that the supremum being absorbed is finite.
An inequality involving an infinite supremum does not justify absorption. This
is the scalar substitute for the sequence-space continuation argument.

The formula for \(g\) needs no differential equations course. For example,
\(g''=g\) implies that \(g'+g\) has derivative equal to itself. The original
first-order calculation then solves for \(g\) by an integrating factor.

## A direct extension of the original first-order theorem

Let \(L=aD+b\), with real smooth coefficients and \(a\) nowhere zero on \(I\).
Choose \(x_*\in I\) and put

\[
\Phi(x)=\int_{x_*}^x\frac{dt}{a(t)},\qquad
w(x)=\exp\left(\int_{x_*}^x\frac{b(t)}{a(t)}\,dt\right).
\]

The original coordinate change gives

\[
F(y)=w(\Phi^{-1}(y))f(\Phi^{-1}(y)),
\qquad
F^{(n)}(\Phi(x))=w(x)L^nf(x).
\]

Apply the even-derivative theorem to \(F\).

**Corollary.** If \((L^2)^nf\) converges pointwise, its limit is smooth and has
the form

\[
g(x)=\frac{Ae^{\Phi(x)}+Be^{-\Phi(x)}}{w(x)}.
\]

Every such function occurs, by taking \(f=g\). The convergence includes all
derivatives uniformly on compact subintervals.

This enlarges the original one-parameter family of limits to a two-parameter
family. It also introduces a useful distinction: \(L^2g=g\) does not require
\(Lg=g\). For \(L=D\), the function \(e^{-x}\) is fixed by \(D^2\), whereas
its ordinary derivatives alternate in sign.

This is a meaningful project extension using a transformation already understood.
It does not classify arbitrary second-order scalar operators: not every such
operator is the square of a real first-order operator.

## A focused research direction: how many points need convergence?

Keep boundedness and convergence separate. Pointwise boundedness everywhere is
still an assumption in the statements below; the question is whether convergence
itself must be assumed at every point.

### A warm-up available from the original theorem

If all ordinary derivatives are pointwise bounded on \(I\) and
\(f^{(n)}(x_*)\to c\) at just one point, the original entire-extension theorem
and Taylor's formula give

\[
f^{(n)}(x)=\sum_{j=0}^\infty
 f^{(n+j)}(x_*)\frac{(x-x_*)^j}{j!}
\longrightarrow ce^{x-x_*}.
\]

The convergence, including every derivative, is uniform on compact intervals.
This is an accessible strengthening of the way the original result was stated.

### Two-point convergence for even derivatives

Assume the even derivatives are pointwise bounded everywhere. Suppose their
values converge at \(a,b\in I\), with

\[
0<b-a<2\sqrt2.
\]

There is a direct proof that the even derivatives then converge smoothly locally
throughout \(I\).

Let \(g''=g\) be the explicit function matching the two limiting endpoint
values, and put \(e_n=u_n-g\). On \([a,b]\), define

\[
E_n=\sup|e_n|,\qquad
\epsilon_n=\max\{|e_n(a)|,|e_n(b)|\},\qquad
q=\frac{(b-a)^2}{8}<1.
\]

The scalar endpoint estimate gives

\[
E_n\le\epsilon_n+qE_{n+1}.
\]

The even-derivative boundedness theorem makes \((E_n)\) bounded. Iterating the
inequality yields

\[
E_n\le\frac{\sup_{j\ge n}\epsilon_j}{1-q}\longrightarrow0.
\]

Uniform derivative bounds give convergence of derivatives in the interval's
interior. Taylor expansion at an interior point, using the entire extension and
the simultaneous bounds on all derivative coefficients, propagates this to
every compact subinterval of \(I\).

This gives a concrete first proposition to write and check. Possible next
questions include improving the sufficient spacing bound, obtaining error
estimates, and transferring sampling conditions through the first-order
coordinate change.

At spacing \(\pi\), there is an obstruction: \(f(x)=\sin x\) has bounded
even derivatives everywhere, and all its even derivatives vanish at both
\(0\) and \(\pi\), but they alternate at other points. Thus an unrestricted
two-point assertion is false. This example alone does not classify larger
spacings.

The number \(2\sqrt2\) comes from the elementary estimate, not from a claim of
optimality. Improving a sufficient spacing bound toward \(\pi\) is a natural
follow-up, but none of these statements is asserted to be previously unknown.
Two-point even-derivative data belong to the classical subject of Lidstone
interpolation. A literature review is necessary before making novelty claims.

## Other accessible extensions, if a different direction is preferable

### Analytic input and arbitrary derivative powers

**Target theorem.** Let \(r\ge1\) and let \(f:I\to\mathbb R\) be real
analytic. If \(f^{(rn)}\) is pointwise bounded, \(f\) extends to an entire
function with all derivatives locally uniformly bounded simultaneously. If
\(f^{(rn)}\) converges pointwise, its limit is smooth and satisfies
\(g^{(r)}=g\), with convergence of every derivative on compact subintervals.

An elementary route is Baire category to obtain uniform bounds on one interval,
Taylor interpolation to bound the missing derivative orders, and Taylor's
theorem to obtain a local entire extension. The real-analytic identity theorem
identifies that extension with \(f\) on all of \(I\). No ODE in a Banach space
is needed.

This is an all-orders result, but the analytic-input hypothesis is substantive.
It cannot be presented as a result for arbitrary smooth input. Its relationship
to classical derivative-interpolation results needs appropriate attribution.

### A sign condition and arbitrary derivative powers

**Target theorem.** Suppose \(f\in C^\infty(I;\mathbb R)\), the sequence
\(f^{(rn)}\) is pointwise bounded, and every selected derivative has a constant
sign throughout \(I\), with that sign allowed to vary with \(n\). Then the
same boundedness and convergence conclusions hold. In particular, it suffices
that every selected derivative is nonnegative.

The key is elementary polynomial interpolation. If \(h^{(r)}\ge0\), interpolation
at \(r\) points to the left of a compact interval bounds \(h\) from below
there. Interpolation using \(r-1\) points to the left and one to the right
bounds it from above. The signs follow from the interpolation remainder,
proved by repeated Rolle's theorem.

Apply this to \(h=\varepsilon_n u_n\), choosing \(\varepsilon_n\) so that
\(h^{(r)}=\varepsilon_n u_{n+1}\ge0\). The interpolants depend on only
\(r+1\) fixed sample values, which are bounded uniformly in \(n\). This gives
local uniform orbit bounds; Taylor interpolation supplies the missing
derivatives. This proof route does not need the general positive factorization
of variable-coefficient operators used in Section 6 of the manuscript.

An initial paper could prove just the case \(r=3\). The examples
\(f=e^x\) and \(f=e^{\alpha x}\), \(0<\alpha<1\), show that the hypotheses
allow both a nonzero fixed limit and decay to zero. The same argument transfers
to powers of regular real first-order operators, since the integrating factor
is positive.

### Singular first-order operators: a separate, closely related paper

The original \(x^2D\) proof extends naturally to \(x^mD\), \(m\ge2\), using

\[
\tau(x)=-\frac{1}{(m-1)x^{m-1}}.
\]

On each half-line, the candidate limit is \(Ce^{\tau(x)}\). A side where
\(\tau\to+\infty\) at zero forces \(C=0\), by the same Taylor-series
averaging argument used in the original paper. On a side where
\(\tau\to-\infty\), every derivative of \(e^\tau\) tends to zero, so the
mode extends smoothly and flatly by zero.

For \(x^mD\), even \(m\) permits a nonzero mode only on the positive side;
odd \(m\) permits independent flat modes on both sides. Thus \(x^3D\) gives a
particularly natural next example beyond \(x^2D\).

A further target is \(a(x)D\) with a finite-order zero of order at least two,
using \(a(x)=(x-z)^m c(x)\), \(c(z)\ne0\), and asymptotics of \(\int dx/a(x)\).
General simple zeros and general zeroth-order terms can be postponed. Even
first-order scalar proofs become more involved there; restricting to scalar
values does not make every singular classification immediate.

For this direction, a coherent title would be *Zeros of the Leading Coefficient
and Limits of First-Order Iterates*. Its core would be explicit examples,
flatness, asymptotic estimates, and gluing across zeros. It should not be
combined with every higher-derivative topic above.

## A possible manuscript outline

Working title: *Pointwise Limits of Real Differential-Operator Iterates:
Positive Results and a Singular Counterexample*.

| Section | Content | Approximate length |
| --- | --- | --- |
| 1 | Original derivative result and the danger of exchanging limits and derivatives | 2 pages |
| 2 | Taylor interpolation and the elementary endpoint estimate | 2 pages |
| 3 | Scalar Baire proof for even derivatives, with attribution to Adams | 3–4 pages |
| 4 | Squares of the original regular first-order operators; explicit limits | 2 pages |
| 5 | Real-analytic input and arbitrary derivative powers | 2–3 pages |
| 6 | An explicit singular first-order counterexample | 2–3 pages |
| 7 | Limitations and remaining questions | 1 page |

An estimated 14–18 pages is a planning target, not a requirement. Use full
explanations rather than compressing proofs to meet a page count.

Sampling questions and sign conditions can be subsequent projects. If a broader
singular classification becomes the main interest, choose the separate
first-order outline instead of expanding every part of this one.

## What to postpone from the unified manuscript

- Banach-valued functions and operator-valued coefficients.
- Sequence-valued ODEs and abstract continuation in function spaces.
- Arbitrary smooth variable-coefficient second-order operators, unless the
  scalar core is already complete and the required ODE facts are proved.
- The full sparse-derivative counterexample and its exceptional set analysis.
- General positive factorization in arbitrary order.
- The planar Laplacian construction and Runge approximation.
- The countable commuting-operator theorem, unless it becomes the subject of a
  separate paper with a self-contained uniqueness lemma.

There is no need to remove all differential equations from the mathematics.
The point is to prove the few elementary identities and uniqueness facts used,
rather than assume a differential equations course or import a general theory.
Likewise, convergence of all derivatives on compact intervals can be defined
directly; a course on locally convex spaces is unnecessary.

## Status and sources

- The original DRP's derivative, regular first-order, \(xD\), and \(x^2D\)
  results are the foundation, not new contributions of this proposal.
- The scalar even-derivative theorem has prior work by Adams. The suggested
  proof architecture is intended to be checked and written in the students'
  own words.
- The restricted all-orders results and monomial extensions are proposed
  undergraduate targets already related to results in the unified draft.
- The sampling discussion supplies explicit proof routes and research questions;
  it is not a statement that the questions are open or the propositions novel.
- A manageable paper with complete, independently understood proofs is the first
  deliverable. Publication novelty requires a separate, focused priority review.

Sources for follow-up:

1. T. Tao's answer to [Paul Cusson's MathOverflow question](https://mathoverflow.net/questions/413165/does-iterating-the-derivative-infinitely-many-times-give-a-smooth-function-whene),
   for the original entire-extension argument.
2. S. Adams, [*Paul Cusson's question*](https://www-users.cse.umn.edu/~adams005/PaulCussonQ/ptbddevenderivs.pdf),
   especially Theorems 31–42 and 57, for the scalar even-derivative argument.
3. M. Waldschmidt, [*On transcendental entire functions with infinitely many
   derivatives taking integer values at two points*](https://arxiv.org/abs/1912.00173),
   especially its introduction and discussion of Lidstone polynomials. Its main
   theorem concerns integer-valued derivative data, not the convergence question
   proposed here; it identifies relevant literature rather than settling priority.
4. The local unified draft, Sections 2–3, 5, and 6, as a source of candidate
   statements. Its independent verification and priority review remain unfinished.
