# Analytic input for differential operators with a vanishing leading coefficient

Research note, 18 October 2026.

## Result

Let \(I\subset\mathbb R\) be a nonempty open interval, and let
\[
Lh=\sum_{j=0}^{m}a_jh^{(j)},\qquad m\geq1,
\]
where the coefficients are real analytic on \(I\) and \(a_m\not\equiv0\).
Let \(f\) be real analytic on \(I\), and put \(u_n=L^nf\), including \(u_0=f\).
Zeros of \(a_m\) are allowed, with no restriction on their multiplicities or on the lower-order coefficients there.

**Boundedness theorem.** If \((u_n(x))_{n\geq0}\) is bounded for every \(x\in I\), then for every compact interval \(K\subset I\) and every integer \(q\geq0\),
\[
\sup_{n\geq0}\sup_{x\in K}|u_n^{(q)}(x)|<\infty.
\]
More precisely, the iterates extend holomorphically to a common connected complex neighborhood of \(I\), on which they form a locally bounded family.

**Convergence theorem.** If \(u_n\to g\) pointwise on \(I\), then \(g\) is real analytic,
\[
Lg=g,\qquad u_n\longrightarrow g\quad\text{in }C^\infty_{\mathrm{loc}}(I).
\]
The latter statement means that, for every compact interval \(K\subset I\) and every \(q\geq0\),
\[
\sup_{x\in K}|u_n^{(q)}(x)-g^{(q)}(x)|\longrightarrow0.
\]

The proof below establishes these statements directly. The literature search located relevant continuation methods, but did not locate this exact theorem. This note does not establish a novelty claim.

## 1. A uniform bound on one real interval

Choose a compact interval \(J_0\subset I\) of positive length on which \(a_m\) does not vanish. Such an interval exists because \(a_m\not\equiv0\). The closed sets
\[
E_N=\{x\in J_0: |u_n(x)|\leq N\text{ for every }n\geq0\},\qquad N=1,2,\ldots,
\]
cover \(J_0\). Baire's theorem gives an interval \(J=[\alpha,\beta]\subset J_0\), with \(\alpha<\beta\), and a constant \(M\) such that
\[
\|u_n\|_J\leq M\qquad(n\geq0).
\]
Here \(\|h\|_J=\sup_{x\in J}|h(x)|\).

We need uniform bounds for the first \(m-1\) derivatives on this interval. The following scaled version of the paper's interpolation estimate provides them.

**Interpolation estimate.** There is a constant \(C_m\), depending only on \(m\), such that for \(h\in C^m(J)\),
\[
\|h^{(j)}\|_J
\leq C_m\delta^{-j}\|h\|_J+
C_m\delta^{m-j}\|h^{(m)}\|_J,
\qquad 0\leq j<m,
\tag{1}
\]
whenever \(0<\delta\leq(\beta-\alpha)/(2m)\).

To prove this, fix \(x\in J\). Choose \(\varepsilon=1\) if \(x\leq(\alpha+\beta)/2\), and \(\varepsilon=-1\) otherwise. All the points \(x+\varepsilon i\delta\), \(1\leq i\leq m\), belong to \(J\). Taylor's formula gives
\[
h(x+\varepsilon i\delta)
=\sum_{j=0}^{m-1}\frac{(\varepsilon i)^j}{j!}\delta^jh^{(j)}(x)+R_i,
\qquad
|R_i|\leq\frac{(m\delta)^m}{m!}\|h^{(m)}\|_J.
\]
The matrix with entries \((\varepsilon i)^j/j!\) is invertible: a polynomial of degree at most \(m-1\) vanishing at the \(m\) distinct points \(\varepsilon,2\varepsilon,\ldots,m\varepsilon\) is zero. Multiplication by its inverse proves (1), with a constant depending only on \(m\). Taking a maximum over the two choices of sign makes the constant independent of \(x\).

On \(J\), set
\[
c=\frac1{a_m},\qquad b_j=-\frac{a_j}{a_m}\quad(0\leq j<m).
\]
The orbit relation \(Lu_n=u_{n+1}\) becomes
\[
u_n^{(m)}=cu_{n+1}+\sum_{j=0}^{m-1}b_ju_n^{(j)}.
\tag{2}
\]
Write \(H_{n,j}=\|u_n^{(j)}\|_J\). Using (1), (2), and \(H_{n,0}\leq M\), we get
\[
H_{n,m}\leq
\|c\|_JM+
C_mM\sum_{j<m}\|b_j\|_J\delta^{-j}
+C_mH_{n,m}\sum_{j<m}\|b_j\|_J\delta^{m-j}.
\]
Choose a fixed positive \(\delta\) small enough that the coefficient of \(H_{n,m}\) on the right is at most \(1/2\). This is possible because every exponent \(m-j\) is positive. Moving that term to the left gives a bound independent of \(n\) for \(H_{n,m}\). Equation (1) then bounds all \(H_{n,j}\), \(j<m\), uniformly in \(n\).

In particular, at any chosen \(x_*\in(\alpha,\beta)\),
\[
M_*:=\sup_{n\geq0,\,0\leq j<m}|u_n^{(j)}(x_*)|<\infty.
\tag{3}
\]
The absorption argument is applied to each finite number \(H_{n,m}\) before taking a supremum over \(n\); it does not assume the desired uniform derivative bound.

## 2. A common complex neighborhood

The finitely many real-analytic functions \(f,a_0,\ldots,a_m\) extend holomorphically to a common connected open set \(\Omega\subset\mathbb C\) containing \(I\).

For completeness, take sufficiently small disks centered at each point of \(I\), with real diameters contained in \(I\), on which all these functions have holomorphic extensions. Two intersecting such disks have a real interval in their intersection. Their extensions agree there, and hence agree on the intersection by the identity theorem. They therefore glue on the union of the disks. This union is connected because each disk meets the connected interval \(I\).

Every \(u_n=L^nf\) is holomorphic on this same \(\Omega\): finite differentiation, multiplication, and addition preserve holomorphy on the domain. Let
\[
Z=\{z\in\Omega:a_m(z)=0\}.
\]
The set \(Z\) is discrete. On \(\Omega\setminus Z\), the functions \(c,b_0,\ldots,b_{m-1}\) in (2) are holomorphic.

## 3. Propagating a bound by Taylor coefficients

This is the main additional lemma.

Suppose \(\overline{D(z_*,R)}\subset\Omega\setminus Z\), and suppose
\[
\sup_{n\geq0,\,0\leq j<m}|u_n^{(j)}(z_*)|\leq M_0.
\tag{4}
\]
We will obtain a uniform bound on a smaller disk whose radius depends on the coefficients and \(R\), but not on \(M_0\) or \(n\).

Put \(v_{n,j}=u_n^{(j)}\), for \(0\leq j<m\). Then
\[
v_{n,j}'=v_{n,j+1}\quad(j<m-1),\qquad
v_{n,m-1}'=cv_{n+1,0}+\sum_{j=0}^{m-1}b_jv_{n,j}.
\tag{5}
\]
Expand these holomorphic functions around \(z_*\):
\[
v_{n,j}(z)=\sum_{k\geq0}v_{n,j,k}(z-z_*)^k,
\quad
c(z)=\sum_{\ell\geq0}c_\ell(z-z_*)^\ell,
\quad
b_j(z)=\sum_{\ell\geq0}b_{j,\ell}(z-z_*)^\ell.
\]
Choose
\[
B=\max\left\{1,
\sup_{\overline{D(z_*,R)}}|c|+
\sum_{j<m}\sup_{\overline{D(z_*,R)}}|b_j|\right\}.
\]
Cauchy's estimates give
\[
|c_\ell|+\sum_{j<m}|b_{j,\ell}|\leq BR^{-\ell}.
\]
Define \(M_k=\sup_{n,j}|v_{n,j,k}|\). Comparing coefficients in (5) gives
\[
(k+1)M_{k+1}\leq B\sum_{\ell=0}^kR^{-\ell}M_{k-\ell}.
\tag{6}
\]
For the equations \(v_{n,j}'=v_{n,j+1}\), this follows from the \(\ell=0\) term and \(B\geq1\). For the last equation, it follows by multiplying the Taylor series. In particular, induction starting from (4) proves that all the suprema \(M_k\) are finite.

Set
\[
A=\max\{2/R,2B\}.
\]
Induction in (6) gives \(M_k\leq M_0A^k\). Indeed, if the bound holds up to \(k\), then
\[
(k+1)M_{k+1}
\leq BM_0A^k\sum_{\ell=0}^k(RA)^{-\ell}
\leq2BM_0A^k
\leq M_0A^{k+1}.
\]
Consequently,
\[
\sup_{n,j}|v_{n,j}(z)|
\leq\sum_{k\geq0}M_0A^k|z-z_*|^k
\leq2M_0
\qquad\left(|z-z_*|\leq\frac1{2A}\right).
\tag{7}
\]
All Taylor expansions used here are expansions of already defined holomorphic functions, with radius at least \(R\); the smaller radius \(1/(2A)\) is at most \(R/4\).

## 4. Paths around zeros and bounds inside circles

The domain \(\Omega\setminus Z\) is path connected. One can join two points by a polygonal path in \(\Omega\), and replace small portions of the path by detours around the finitely many zeros it meets. Finiteness follows because a compact subset of \(\Omega\) contains only finitely many points of the discrete zero set.

Fix a path in \(\Omega\setminus Z\) from \(x_*\) to any prescribed point \(z\). Its image is compact. Choose \(R>0\) such that every closed disk of radius \(R\) centered on the path is contained in \(\Omega\setminus Z\). The union of these disks is compact, so \(c,b_0,\ldots,b_{m-1}\) have finite uniform bounds there. Thus one choice of \(B\), and hence of \(A\), works at every center along the path.

Starting from (3), apply (7) along finitely many successive centers on the path, with consecutive centers less than \(1/(2A)\) apart. Each step multiplies the bound by at most two. After finitely many steps we obtain a neighborhood of \(z\) on which all \(u_n\) are uniformly bounded. This proves local boundedness on \(\Omega\setminus Z\).

Now fix \(z_0\in Z\). Choose \(\rho>0\) such that \(\overline{D(z_0,\rho)}\subset\Omega\) and this disk contains no other zero. Its boundary circle is a compact subset of \(\Omega\setminus Z\). A finite cover by neighborhoods with uniform orbit bounds gives a constant \(C\) such that
\[
|u_n(z)|\leq C\qquad(n\geq0,\ |z-z_0|=\rho).
\]
Each \(u_n\) is holomorphic throughout the disk, including \(z_0\). The maximum-modulus principle therefore gives
\[
|u_n(z)|\leq C\qquad(n\geq0,\ |z-z_0|\leq\rho).
\tag{8}
\]
This proves local boundedness on all of \(\Omega\).

The decisive point is that the normalized coefficients in (2) can have poles at \(z_0\), while the original iterates \(u_n\) do not. Division by \(a_m\) was used only away from its zeros. The maximum-modulus principle supplies the estimate at a zero without division there.

## 5. Derivative bounds, convergence, and analyticity

Local boundedness and compactness bound all the \(u_n\) uniformly on every compact subset of \(\Omega\). For any compact real interval \(K\subset I\), choose \(r>0\) so that its closed complex \(r\)-neighborhood is contained in \(\Omega\), and let \(C\) bound all iterates there. Cauchy's estimates give
\[
\sup_{x\in K}|u_n^{(q)}(x)|\leq Cq!r^{-q}
\qquad(n,q\geq0).
\tag{9}
\]
This proves the boundedness theorem.

Suppose now that \(u_n\to g\) pointwise on \(I\). The elementary convergence lemma already proved in the Typst paper gives \(g\in C^\infty(I)\) and convergence locally uniformly with every derivative. Here is the argument in brief:

1. Uniform first-derivative bounds give equicontinuity. A finite cover of a compact interval, together with pointwise convergence at the finitely many centers, proves uniform convergence there.
2. To pass from convergence of the \(q\)-th derivatives to convergence of the \((q+1)\)-st derivatives, apply Taylor's estimate to \(h=u_n^{(q)}-u_p^{(q)}\). For compact intervals \(K\) in the interior of \(J\), and sufficiently small \(t>0\),
   \[
   \|h'\|_K\leq\frac2t\|h\|_J+\frac t2\|h''\|_J.
   \]
   First make the second term small using the uniform bound on \(h''\), then make the first small using the induction hypothesis. This proves that each derivative sequence is locally uniformly Cauchy.
3. The fundamental theorem of calculus identifies the resulting limits as successive derivatives of \(g\).

Passing to the limit in \(Lu_n=u_{n+1}\) now yields \(Lg=g\), including at zeros of \(a_m\).

To see that \(g\) is analytic, fix \(x_0\in I\) and choose \(r>0\) such that \([x_0-r,x_0+r]\subset I\) and \(\overline{D(x_0,2r)}\subset\Omega\). Let \(C\) bound all \(u_n\) on this disk. Cauchy's estimates on disks of radius \(r\) centered at points of \([x_0-r,x_0+r]\), followed by passage to the limit, give
\[
|g^{(q)}(x)|\leq Cq!r^{-q}\qquad(|x-x_0|\leq r).
\]
Taylor's remainder at \(x_0\) is therefore at most
\[
C\left(\frac{|x-x_0|}{r}\right)^{N+1}
\]
after degree \(N\). It tends to zero for \(|x-x_0|<r\), proving analyticity.

## 6. Scope and examples

### Relation to the original project

The theorem covers \(D^r\), \(xD\), \(x^2D\), and every positive-order scalar differential operator with real-analytic coefficients and a leading coefficient that is not identically zero. It recovers the versions of the original project's conclusions with analytic coefficients and analytic input. The original smooth-input results remain stronger concerning input regularity in the cases they cover.

It also applies to iterates \(L^{rn}f\) for each fixed positive integer \(r\): the operator \(L^r\) has order \(mr\), analytic coefficients, and leading coefficient \(a_m^r\not\equiv0\).

### The existing singular counterexample becomes a direct comparison

The paper's operator
\[
Lh=-\frac{x^3}{2}h'+(1-x^2)h
\]
satisfies the new theorem's coefficient hypotheses. Thus every analytic input whose orbit converges pointwise has an analytic limit and locally uniform convergence of every derivative.

But for the smooth input
\[
f(x)=1-e^{-1/x^2}\quad(x\ne0),\qquad f(0)=1,
\]
the existing full-orbit formula gives
\[
L^nf(x)=\frac1{x^2}\int_0^1s^n e^{-(1-s)/x^2}\,ds\quad(x\ne0),
\qquad L^nf(0)=1.
\]
The limit is the indicator of \(\{0\}\). This input is not analytic at zero. In the positive proof, analyticity there is what makes each iterate holomorphic inside the circle used in (8).

### Positive order is necessary

The assertion is false for arbitrary order-zero operators, even with analytic input. On \((-1,1)\), let
\[
Lh=(1-x^2)h,\qquad f=1.
\]
Then \(L^nf=(1-x^2)^n\) converges pointwise to the indicator of \(\{0\}\). This is why the theorem requires actual order \(m\geq1\), with \(a_m\not\equiv0\).

### An entire extension is not a general conclusion

On \(\mathbb R\), take
\[
f(x)=\frac1{1+x^2},\qquad
L=D+1+\frac{2x}{1+x^2}.
\]
Both the input and coefficients are real analytic, and \(Lf=f\). The orbit is constant, but \(f\) has no entire extension, since its complex extension has poles at \(i\) and \(-i\). The stronger entire-extension conclusion for \(D^r\) is specific to that setting.

## 7. Literature and proof difficulty

- [Terence Tao's answer to Paul Cusson's question on MathOverflow (2022)](https://mathoverflow.net/questions/413165/does-iterating-the-derivative-infinitely-many-times-give-a-smooth-function-whene/413247) proves the original ordinary-derivative analyticity result using pointwise bounds, Baire category, and Taylor estimates. It supplies the starting model for the present argument.
- The local AI-generated manuscript, `pointwise_iterates_unified.tex`, Section 7.2, treats the analytic-input problem with a nowhere-zero leading coefficient using a bounded-sequence-valued differential equation. The direct coefficient estimate above replaces that step and permits propagation along complex paths.
- [Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Chapter 4, especially Theorem 4.7](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf), develops continuation of analytic linear differential equations along paths using local radii independent of initial values. This supports the continuation method; it does not state the theorem about the whole family of iterates proved here.
- [Stefan Fürdös and Gerhard Schindl, *The Theorem of Iterates for elliptic and non-elliptic Operators* (2022)](https://arxiv.org/abs/2103.02285), studies regularity characterized by growth estimates on iterates, including analytic-vector and ultradifferentiable settings. Its hypotheses and conclusions differ from the pointwise-convergence question here; it is related literature rather than a direct citation for this theorem.

The searches examined analytic differential-operator iterates, pointwise boundedness, singular leading coefficients, and bounded holomorphic orbits. They did not identify a source stating exactly the two theorems above. Attribution and novelty require further checking before a publication claim.

For an advanced undergraduate with the stated background, this looks feasible as the main theorem of the continuation paper. The required ingredients are Baire category, Taylor's theorem, finite-dimensional linear algebra, the identity theorem, Cauchy's estimates, and the maximum-modulus principle. The technical center is Section 3: deriving a Taylor-coefficient recurrence and choosing a radius independent of the iterate number. Understanding that estimate is a focused task; an ODE or functional-analysis course is not a prerequisite for this proof.

A useful reading order is to work through Section 3 first for \(m=1\), where the relation is simply \(u_n'=cu_{n+1}+b_0u_n\), then understand the circle argument in Section 4. After that, the higher-order case adds a finite list of derivatives and the interpolation estimate in Section 1.
