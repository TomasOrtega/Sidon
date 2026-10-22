# A positive smoothed prime detector from the actual logarithmic explicit formula

This is the checked all-length prime-interval proof. It uses the literal
logarithmically smoothed formula in RiemannGaussian, the project's
unconditional actual-zero density estimate, and an absolutely convergent
reciprocal-square zero mass. Every input is connected in Lean through
`Sidon.exists_primeIntervalBound_two_thirds`; its conclusion gives a
prime in `[x-128*x^(2/3),x]` for every sufficiently large real `x`.
No truncated unsmoothed formula, good contour height, or local zero-count
estimate is needed.

Fix the implemented parameters `A=23/8`, `tau=17/50`, and `r=128`.
The density proof uses the actual critical-line exponent `c=3/16`,
obtained from the checked source Weyl estimate by logarithm absorption.
The numerical requirements are

\[
 A\tau<1,\qquad r/3-(r-2)\tau<0.
\]

The two implemented margins are `391/400<1` and `-13/75<0`.
A sharper density endpoint with `A=11/4` would also allow
`tau=7/20,r=64`, giving margins `77/80<1` and `-11/30<0`;
this optional parameter choice is not the theorem claimed by the
formal endpoint.

## 1. The exact inputs

For real `t≥0`, the primary formula is an identity for the literal sum

\[
 F_1(t)=\sum_{n\le e^t}\Lambda(n)(t-\log n)
       =e^t-1-\log(2\pi)t-Z_1(t)+Q_1(t),
\tag{1}
\]

where

\[
 Z_1(t)=\sum_\rho m_\rho{e^{\rho t}-1\over\rho^2}.
\]

Here the sum ranges over distinct actual nontrivial zeta zeros, with
analytic multiplicity `m_rho`. The source declarations are
`RosserSchoenfeldExplicitFormula.finite_prime_explicitFormula` and
`RosserSchoenfeldZeroPrimitive.value`. The nontrivial-zero sum is
absolutely convergent on every compact nonnegative `t` interval. A
sufficient bound, also needed below, is

\[
 M:=\sum_\rho {m_\rho\over|\rho|^2}<\infty.
\tag{2}
\]

Only finiteness is needed; no verified numerical zero table or numerical
value of `M` is required. Since zeta is continuous and nonzero at zero,
and its zero set is closed, there is also a positive lower bound for
`|rho|` over these zeros. This makes all higher reciprocal powers
summable as well.

The trivial-zero term `Q_1` consists of a convergent series of terms
proportional to `(e^(-2jt)-1)/(2j)^2`, together with elementary
polynomials of degree at most one, with signs depending on the source's
normalization. Their exact signs are immaterial to the estimates below,
but they must be matched in the extracted identity.

The density and zero-free inputs are the uniform estimate

\[
 N(\sigma,T)\le K T^{A(1-\sigma)}(\log T)^B
 \quad(0\le\sigma\le1,\ T\ge T_0)
\tag{3}
\]

and an all-height width `eta(T)>0` such that every zero up to height
`T` has `beta≤1-eta(T)` and

\[
 \eta(T)\log T/\log\log T\longrightarrow\infty.
\tag{4}
\]

The checked density uses `B=11`; the reduction below works for every
fixed natural `B`. Thus the logarithmic loss in the formal mollifier
proof causes no change in the prime-gap exponent. The zero-free width
is the checked unshifted Vinogradov–Korobov expression
`(1/20000)/(log(T)^(2/3)*loglog(T)^(1/3))`, after an eventual threshold.

## 2. Integrating the formula a fixed number of times

Let `J f(t)=integral_0^t f(u)du` and apply `J^(r-2)` to (1). All
integrations take place on compact nonnegative intervals. The finite
prime sum has only finitely many contributing indices throughout such
an interval. Its integrated value is

\[
 F_{r-1}(t)=\sum_n\Lambda(n)
        {(t-\log n)_+^{r-1}\over(r-1)!}.
\tag{5}
\]

Terms with `n>e^t` vanish. The `n=1` term is zero because `Lambda(1)=0`.
The identity follows by integrating the truncated power directly;
`log n≥0` for every relevant positive integer.

For one nonzero complex `rho`, repeated integration gives

\[
 J^{r-2}{e^{\rho t}-1\over\rho^2}
 ={e^{\rho t}-\sum_{j=0}^{r-2}(\rho t)^j/j!\over\rho^r}.
\tag{6}
\]

This is proved by induction using the fundamental theorem of calculus.
On `0≤t≤L`, the original summands are bounded by
`m_rho*(e^L+1)/|rho|^2`, a summable majorant from (2). Dominated
convergence therefore justifies every integration through the zero sum.
The polynomial coefficients in (6) also converge absolutely: their
reciprocal exponents are at least two, and the uniform lower bound for
`|rho|` reduces each higher power to (2).

The same argument applies to the trivial-zero sum on compact intervals.
The integrated main term is `e^t` plus a polynomial of degree at most
`r-3`; integrated constants have degree `r-2`, and the integrated linear
term has degree `r-1`.

Define the forward difference `Delta_delta f(t)=f(t+delta)-f(t)`.
Its `r`th iterate annihilates every polynomial of degree at most `r-1`.
Applying it to the integrated identity therefore yields

\[
 D(t):=\Delta_\delta^r F_{r-1}(t)
 =e^t(e^\delta-1)^r
 -\sum_\rho m_\rho e^{\rho t}
          {(e^{\rho\delta}-1)^r\over\rho^r}
 +E_{\rm triv}(t).
\tag{7}
\]

Only a fixed finite linear combination is taken, so it commutes with
every absolutely convergent sum. No differentiation of a zero series is
needed.

## 3. Positivity, support, and the detector's maximum

For `a≥0`, write

\[
 b_{r,\delta}(t-a)=\Delta_\delta^r{(t-a)_+^{r-1}\over(r-1)!}.
\]

For `r≥2` and `delta>0`, this function is nonnegative, vanishes outside
`-r*delta≤t-a≤0`, and is at most `delta^(r-1)`.
Here is a proof avoiding a large explicit alternating polynomial.
Repeated fundamental theorem of calculus gives

\[
 \Delta_\delta^{r-1}{(t-a)_+^{r-1}\over(r-1)!}
 =\int_{[0,\delta]^{r-1}}
      1_{\{t+u_1+\cdots+u_{r-1}>a\}}\,du.
\]

The boundary hyperplane has measure zero, so the choice of strict or
nonstrict indicator is irrelevant. The last difference replaces the
indicator by the difference between its values at `t+delta` and `t`.
That difference lies in `[0,1]`; integrating over a box of volume
`delta^(r-1)` proves positivity and the maximum bound. If `t>a`, both
indicators equal one. If `t+r*delta<a`, both equal zero. At the boundary
the same zero conclusion follows by the hyperplane's null measure.
Thus

\[
 D(t)=\sum_n\Lambda(n)b_{r,\delta}(t-\log n)
\tag{8}
\]

is a nonnegative sum supported on the logarithmic interval
`[t,t+r*delta]`.

## 4. Parameter choice and the main term

Given sufficiently large real `x`, put

\[
 \delta=x^{-1/3},\quad t=\log x-r\delta,\quad T=x^\tau.
\]

Eventually `t≥1` and `r*delta≤log 2`. Since `e^delta-1≥delta`,

\[
 e^t(e^\delta-1)^r\ge(x/2)\delta^r.
\tag{9}
\]

The detector's logarithmic support is `[log x-r*delta,log x]`, hence
all detected integers lie below `x`. The lower real endpoint satisfies

\[
 xe^{-r\delta}\ge x(1-r\delta)=x-rx^{2/3},
\tag{10}
\]

using `e^-u≥1-u`. Therefore any detected actual prime proves the desired
all-real interval theorem with the fixed constant `C=r`.

## 5. Low zeros use the existing finite layer bound

For `0≤beta≤1`, the fundamental theorem of calculus gives

\[
 |e^{\rho\delta}-1|\le|\rho|\delta e^{\beta\delta}.
\]

Consequently one zero term with `|gamma|≤T` has absolute value at most

\[
 m_\rho e^{\beta t}\delta^r e^{r\beta\delta}
   =m_\rho\delta^r x^\beta.
\tag{11}
\]

Relative to `x*delta^r`, the sum is exactly bounded by
`sum_(|gamma|≤T) m_rho*x^(beta-1)`. The finite zero-layer theorem,
(3), (4), and `A*tau<1` make this `o(1)`, for any fixed logarithmic
exponent `B`. Conjugate zeros give twice the positive-height bound.
The formal split uses `|rho|<T` on the low side; it is a subset of the
zeros with `|gamma|≤T`, so the same positive-height occurrence bound
applies. Nonrealness of every actual nontrivial zero is checked in
`NontrivialZetaZero.im_ne_zero_of_eta_mass`. Analytic multiplicity is
definitionally `analyticOrderNatAt riemannZeta rho`, and the occurrence
bridge repeats each zero exactly this many times. Thus neither real
zeros nor an assumed simplicity statement are hidden in the doubling.

## 6. High zeros use only the finite reciprocal-square mass

Eventually `delta≤1` and `r*delta≤1`. For any zero,

\[
 |e^{\rho\delta}-1|\le e^{\beta\delta}+1\le2e^{\beta\delta}.
\]

On the complementary formal high side `|rho|≥T`, use
`t+r*delta=log x`, `0≤beta≤1`, and

\[
 \sum_{|\rho|\ge T}m_\rho
  \left|e^{\rho t}{(e^{\rho\delta}-1)^r\over\rho^r}\right|
 \le2^r x\,T^{-(r-2)}M.
\tag{12}
\]

Divide by `x*delta^r`. The remaining power is

\[
 \delta^{-r}T^{-(r-2)}=x^{r/3-(r-2)\tau}=o(1)
\]

by the selected fixed `r`. This is why high-order smoothing matters:
a triangular detector with `r=2` would not give a usable tail bound.
All constants depending on `r` are fixed before `x` tends to infinity.
No estimate with a growing differentiation order is being used.

## 7. Trivial zeros and nonprime powers

For a trivial zero `-2j`, with `j≥1`, use both
`|e^(-2j*delta)-1|≤2j*delta` and
`|e^(-2j*delta)-1|≤1`. Reserve two factors for the reciprocal-square
sum and bound the other `r-2` factors by `delta`. Since `t≥0`,

\[
 \left|e^{-2jt}{(e^{-2j\delta}-1)^r\over(2j)^r}\right|
 \le\frac{\delta^{r-2}}{(2j)^2}.
\]

The checked estimate allows the harmless larger constant
`|E_triv(t)|≤(pi^2/6)*delta^(r-2)`. Relative to `x*delta^r`, this is
`(pi^2/6)*x^(-1/3)`, hence tends to zero. This bound also covers `t=0`
and does not need exponential decay of the trivial-zero tail.

The contribution from nonprime prime powers is at most

\[
 \delta^{r-1}\sum_{n\le x,\ n\text{ not prime}}\Lambda(n)
 \ll\delta^{r-1}\sqrt x\log^2x.
\tag{13}
\]

The normalized bound is `x^-1/6*log^2x=o(1)`. The already checked
`PrimePowerError` estimate suffices, including floor endpoints.
Thus (7), (9), (11)–(13) imply, for all sufficiently large real `x`,
that the detector's prime contribution is positive. Its finite sum of
nonnegative terms then has at least one prime index. By (10), that
prime belongs to `[x-r*x^(2/3),x]`.

## 8. Checked formal modules

| Modules in `Sidon/NumberTheory` | Checked role |
|---|---|
| `BSplineKernel`, `BSplinePrimitive`, `BSplineDetector` | Primitive identity, nonnegative kernel, support, maximum and finite weighted detector |
| `LogSmoothing`, `SmoothingSeries`, `SmoothedMangoldt`, `LogSmoothedMangoldt` | Exact primitive recursion, finite differences, uniformly dominated infinite-series exchanges and actual arithmetic sum |
| `RiemannGaussian/RosserSchoenfeldExplicitFormula`, `SmoothedExplicitFormula` | Literal unconditional log-smoothed identity and its arbitrary-order spectral smoothing |
| `SpectralKernelBounds`, `SpectralTailBounds`, `NegativeSpectralBounds`, `LowZeroBridge`, `SmoothedZeroBounds` | Actual low-zero occurrence bridge, both signs and analytic multiplicities, high reciprocal-square tail and trivial-zero error |
| `ZetaDensity`, `ZetaZeroFree`, `LogarithmicReserve`, `ZeroDensityLayers`, `ZetaZeroWeight` | Actual all-strip density, all-height zero-free width, finite layers and the vanishing low-zero weight |
| `PrimePowerError`, `SmoothedPrimeDetection`, `SmoothedDetectorEstimate` | Nonprime prime-power removal and extraction of an actual supported prime |
| `PrimeDetectorParameters`, `PrimeGapFromDensity`, `PrimeGapTwoThirds` | Fixed parameters, all relative errors tending to zero, and unconditional `PrimeIntervalBound (2/3) 128` |

The terminal theorem has only existential constants and a sufficiently
large real endpoint; it has no density, zero-free, or explicit-formula
premise. `Sidon/Constructions/MaximumUniformity.lean` combines it with
the checked Bose–Chowla construction and Fourier estimate to prove the
paper's all-length largest-Sidon-set Fourier rate `N^(-1/12)`.
