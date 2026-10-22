# The literal logarithmically smoothed explicit formula

Source: David Sanftenberg's
[RiemannGaussian at 6e969fd](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603),
principally `RosserSchoenfeldLaplace`, `RosserSchoenfeldPrimePrimitive`,
`RosserSchoenfeldZeroPrimitive`, `RosserSchoenfeldTrivialPrimitive`, and
`RosserSchoenfeldExplicitFormula`. These files use Apache 2.0. The complete 275-module extraction has passed the actual project build with
the project binder policy enabled. Post-rewrite kernel audits of the exact
formula, zero mass, conjugation and nonreality contain only the three standard
principles; the preceding VK/Weyl endpoints have the same audit result.

For (x\ge1), the exact formula is

\[
 \sum_{n=1}^{\lfloor x\rfloor}\Lambda(n)\log(x/n)
 =x-1-\log(2\pi)\log x
 -\sum_\rho m_\rho\frac{x^\rho-1}{\rho^2}
 +\sum_{j=1}^\infty\frac{1-x^{-2j}}{4j^2}.                 \tag{1}
\]

The equation is interpreted in \(\mathbb C\), using the real logarithm for
positive bases. The zero sum ranges over distinct actual nontrivial zeros of
mathlib's `riemannZeta`, with analytic multiplicity \(m_\rho\). Both ordinate
signs are present. Every displayed infinite sum converges absolutely; (1)
does not rely on a symmetric-cutoff summation convention.

## Arithmetic side and its transform

Set \(t=\log x\ge0\), and define the nonnegative hinge

\[
 a_n(t)=\Lambda(n)\max(t-\log n,0),\qquad
 A(t)=\sum_{1\le n\le\lfloor e^t\rfloor}a_n(t).
\]

For \(n\ge1\), the hinge vanishes when \(n>e^t\). For \(n=0\), the
von Mangoldt factor is zero. Thus the finite moving sum equals the full
series \(\sum_{n\ge0}a_n(t)\) at each time. On a neighborhood of any fixed
\(t\), all contributing indices lie in one larger finite window. Every
hinge is continuous, including when its argument crosses zero; therefore
\(A\) is continuous despite the floor in its definition. At \(t=0\), its
only possible index is \(n=1\), where \(\Lambda(1)=0\).

For \(\Re s>1\), the damped hinges are absolutely integrable and the sum of
their absolute integrals is finite. Indeed their absolute integral is bounded
by the corresponding integral with damping \(e^{-\Re(s)t}\), whose sum is
a convergent von Mangoldt Dirichlet series divided by \((\Re s)^2\).
This supplies the hypotheses for exchanging the sum and integral.
For a contributing index \(n\ge1\), substitution \(u=t-\log n\) gives

\[
 \int_0^\infty e^{-st}a_n(t)\,dt
 =\Lambda(n)n^{-s}\int_0^\infty ue^{-su}\,du
 =\frac{\Lambda(n)n^{-s}}{s^2}.
\]

The endpoint at \(t=\log n\) contributes nothing, since the hinge is zero
there. Integration by parts evaluates the last integral, with both boundary
terms tending to zero under positive real damping. The absolutely convergent
Euler-product logarithmic derivative yields

\[
 \mathcal L A(s)
 =\int_0^\infty e^{-st}A(t)\,dt
 =-\frac{\zeta'(s)}{s^2\zeta(s)}.                        \tag{2}
\]

Here \(\zeta(s)\ne0\) for \(\Re s>1\). The proof retains the literal
von Mangoldt coefficients and the genuine moving finite prime-power window.

## Absolute convergence of the nontrivial zero primitive

Write \(\rho=\beta+i\gamma\). The checked source zero geometry supplies
\(0<\beta<1\), and its multiplicity is the natural analytic order of
\(\zeta\) at \(\rho\). The complete reflected xi logarithmic-derivative
expansion supplies a summable positive series

\[
 \sum_\rho m_\rho P(\rho),\qquad
 P(\rho)=\frac{1-\beta}{(1-\beta)^2+\gamma^2}
          +\frac{\beta}{\beta^2+\gamma^2}.
\]

Each denominator is positive: its real-part square is strictly positive.
Since \(0<\beta<1\), replacing either squared real part by \(1\)
increases that denominator. Both numerators are nonnegative, so

\[
 P(\rho)\ge\frac{1-\beta}{1+\gamma^2}
               +\frac{\beta}{1+\gamma^2}
           =\frac1{1+\gamma^2}.                         \tag{3}
\]

This estimate uses no verified table of small zeros. To pass from (3) to
reciprocal *norm* squares, use closedness of the actual zeta-zero set and
\(\zeta(0)=-1/2\ne0\). Its complement contains a ball of some radius
\(\epsilon>0\) around zero. Every nontrivial zero therefore satisfies
\(\|\rho\|\ge\epsilon\). Put
\(D=(1+\epsilon^2)/\epsilon^2\). Since
\(\gamma^2\le\|\rho\|^2\) and
\(\epsilon^2\le\|\rho\|^2\),

\[
 1+\gamma^2\le D\|\rho\|^2,
 \qquad
 \frac{m_\rho}{\|\rho\|^2}
 \le D\frac{m_\rho}{1+\gamma^2}
 \le Dm_\rho P(\rho).
\]

Comparison of nonnegative series proves that

\[
 M:=\sum_\rho\frac{m_\rho}{\|\rho\|^2}<\infty.           \tag{4}
\]

The generic comparison proof has compiled and its kernel dependencies are
exactly `propext`, `Classical.choice`, and `Quot.sound`. This replacement
avoids the source's evaluated \(0.0463\) constant and all numerical
certification of zeros through heights \(14\) and \(54\).

Define

\[
 Z(t)=\sum_\rho m_\rho\frac{e^{\rho t}-1}{\rho^2}.
\]

For \(t\ge0\), \(|e^{\rho t}|=e^{\beta t}\le e^t\). Consequently

\[
 \left|m_\rho\frac{e^{\rho t}-1}{\rho^2}\right|
 \le(e^t+1)\frac{m_\rho}{\|\rho\|^2},
 \qquad |Z(t)|\le M(e^t+1).                             \tag{5}
\]

Equation (4) proves absolute convergence. On each bounded positive-time
interval, (5) supplies one summable majorant, so the series converges uniformly
and its sum is continuous. For \(\Re s>1\), the damped majorant is

\[
 M\bigl(e^{(1-\Re s)t}+e^{-\Re(s)t}\bigr),
\]

which is integrable on \((0,\infty)\). This proves integrability of the
complete damped primitive and justifies exchanging its series and integral.

Since \(\rho\ne0\) and \(\Re(s-\rho)>0\), direct exponential integration
of one zero atom gives

\[
 \int_0^\infty e^{-st}\frac{e^{\rho t}-1}{\rho^2}\,dt
 =\frac1{\rho^2}\left(\frac1{s-\rho}-\frac1s\right)
 =\frac1{s\rho(s-\rho)}.
\]

The complete xi logarithmic-derivative difference therefore gives

\[
 \mathcal L Z(s)
 =\frac{(\xi'/\xi)(s)-(\xi'/\xi)(0)}{s^2}.               \tag{6}
\]

Every multiplicity remains in (6), and all exchanges use absolute convergence.

## Trivial zeros and the elementary correction

The complete trivial-zero contribution is

\[
 V(t)=\sum_{j=1}^\infty\frac{1-e^{-2jt}}{4j^2}.
\]

For nonnegative time, every term lies in \([0,1/(4j^2)]\). The reciprocal
square series has sum \(\pi^2/24\), so it proves absolute and uniform
convergence, continuity including at zero, and the bound
\(0\le V(t)\le\pi^2/24\). After positive real damping the same summable
majorant is integrable, permitting termwise transforms. A term is the negative
of the zero atom at \(\rho=-2j\), so its transform follows from the preceding
single-atom calculation.

Set

\[
 B(t)=e^t-1-\log(2\pi)t-Z(t)+V(t).
\]

The elementary part has transform

\[
 \frac1{s(s-1)}-\frac{\log(2\pi)}{s^2}.
\]

The exact gamma-factor logarithmic derivative, the full transformed trivial
series, (6), and the values of the xi logarithmic derivative at zero and one
then cancel to give

\[
 \mathcal L B(s)=-\frac{\zeta'(s)}{s^2\zeta(s)}.          \tag{7}
\]

This step uses the actual gamma and xi factorization. It does not identify
an arbitrary proposed zero measure with the zeta divisor. The source records
the exact constants, including

\[
 (\xi'/\xi)(0)
 =-1-\gamma_E/2+\log2+\tfrac12\log\pi.
\]

## Why equal transforms imply the pointwise formula

By (2) and (7), \(f=A-B\) has zero Laplace transform on the vertical line
\(s=2+iy\). Both damped expressions are integrable, and \(f\) is
continuous on positive time. Extend
\(F(t)=e^{-2t}f(t)\) by zero for \(t\le0\). This is an integrable function
on the real line. At Fourier frequency \(w\), its transform is exactly the
zero Laplace transform at \(2+2\pi iw\). Thus its Fourier transform vanishes
at every frequency. Fourier inversion at each positive continuity point gives
\(F(t)=0\); since \(e^{-2t}\ne0\), \(A(t)=B(t)\).

At time zero both sides vanish term by term, so equality holds for every
\(t\ge0\). Finally \(t=\log x\), \(e^t=x\), and
\(t-\log n=\log(x/n)\) for each positive index in the finite window. This
is (1), including the endpoint case \(x=1\).

The formal terminal is
`RiemannGaussian.RosserSchoenfeldExplicitFormula.finite_prime_explicitFormula`.
Its displayed statement has only `1 ≤ x` as a premise.
