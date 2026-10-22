# RiemannGaussian: semantic audit and checked extraction

Audited source: [dbsanfte/RiemannGaussian at 6e969fd6e9c639eed280c595732248c106187603](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603).
The source pins Lean 4.34.1 and mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. Relevant headers identify
David Sanftenberg as author and copyright holder and use Apache 2.0.
The Sidon worktree uses Lean/mathlib 4.35.0.

## Definitions and surface statements inspected

The main zero-free target is
[RiemannGaussian.ZetaVinogradovSummedZeroFree.exists_eventual_strip](https://github.com/dbsanfte/RiemannGaussian/blob/6e969fd6e9c639eed280c595732248c106187603/RiemannGaussian/ZetaVinogradovSummedZeroFree.lean).

Its nontrivial-zero type is the subtype of complex numbers satisfying

\[
 \zeta(s)=0,\qquad
 \neg\exists n:\mathbb N,\ s=-2(n+1),\qquad s\ne1.
\]

Zeta is literally mathlib's `riemannZeta`. The ordinate height is
\(|t|+2\), its scale is \(\log(|t|+2)\), and its level is the logarithm
of that scale. The width is

\[
 w(C,t)=
 \frac{C}{\log(|t|+2)^{2/3}\,
              \log\log(|t|+2)^{1/3}}.
\]

For every \(0<C<3\pi/10640\), the target asserts that some finite \(T\ge4\)
has the following property: every actual nontrivial zero \(\rho\) with
\(|\Im\rho|\ge T\) satisfies

\[
 w(C,\Im\rho)<\Re\rho<1-w(C,\Im\rho).
\]

Its printed Lean type has no zero-free, cancellation, or density premise
beyond those two coefficient inequalities.

The literal conjugation API is `NontrivialZetaZero.conjugate`.
The separately named `conjugatePartner` is \(1-\overline\rho\).
Multiplicity is exactly `analyticOrderNatAt riemannZeta ρ`, rather
than a supplied or assumed simple multiplicity. Conjugation preserves it.
The selected positive eta-mass argument proves that nontrivial zeros are
nonreal, permitting pairing of both ordinate signs.

## Analytic chain in the VK proof

The signed local zero detector is applied with genuine analytic-disc and
magnitude bounds at \(t\) and \(2t\). The payment inequality is discharged
by an eventual limit. It is not left as an argument of the terminal theorem.

The selected near-one magnitude bound controls literal zeta by

\[
 |\zeta(\sigma+it)|
 \le1048576\,t^{g(n)}(\log t)^{2/3},
 \qquad
 g(n)=40\Delta_n^{3/2},\quad
 \Delta_n=\frac1{4096(2n+1)^2},
\]

on its stated strip above an explicit finite height threshold.
The proof retains the original finite Dirichlet prefix, bounds its dyadic
blocks, and pays the Euler remainder. Degree and height feasibility are
proved in the schedule modules. The terminal starting height is finite,
although unevaluated.

The generic critical-line result is
`RiemannGaussian.ZetaEulerLineBound.bound_abs`.
Specialization to derivative index \(k=1\) uses
`DirichletPowerParameters.line 1 = 1/2` and
`DerivativePowerExponents.alpha 1 = 1/6`, giving

\[
 |\zeta(1/2+it)|\le8192\,|t|^{1/6}\log|t|,\qquad |t|\ge2.
\]

The applications agent has checked the explicit consequence
\(393216|t|^{3/16}\) and extension to bounded ordinates by compactness.
The finite-sum definitions were printed: rotation is
\(\exp(ix)\), and the Dirichlet feature is \(\exp(-s\log n)\).

A crude ready bound used for strip integrability is
`norm_riemannZeta₁_le_etaStrip`:

\[
 \tfrac12\le\Re s\le\tfrac32
 \quad\Longrightarrow\quad
 |\zeta_1(s)|\le8(|\Im s|+20)^2.
\]

Here \(\zeta_1\) is mathlib's entire pole-removed zeta. Analytic expressions
through \(s=1\) must use this extension: literal \((s-1)\zeta(s)\) has
value zero there because mathlib assigns zeta a finite value at its pole,
whereas \(\zeta_1(1)=1\).

## Extraction, imports, and kernel audits

The original VK module import closure contains 1067 modules and 266100
source lines. An initial checked declaration slice reduced it to 1535
source declarations in 242 modules, with 22012 proof lines before headers.

The current expanded extraction adds the exact smoothed explicit formula,
qualitative zero mass, and sign-pairing API. It contains 1825 source
declarations in 275 modules, with 26760 proof lines before headers.
All 275 staged modules compile with `autoImplicit=false` and the
project's Lean/mathlib 4.35.0 toolchain.

The [source manifest](rg-extraction-manifest.json) records every immutable
upstream path and hash, every adapted file hash, all selected declarations,
and their 5885 source dependency edges. Module paths are prefixed by
`Sidon.NumberTheory`; declaration namespaces remain
`RiemannGaussian`. The umbrella imports all 275 source modules.

Repeated explicit Mathlib imports already provided by selected dependencies
were removed: 23048 import lines became 3139. A recursive set-equality check
verifies that each module receives exactly the same original explicit
Mathlib ancestor set.

Proof adaptations are limited to the following:

- two explicit positive real-power arguments replace positivity tactic calls;
- two real parameters previously inferred automatically are explicit binders;
- the indicator-integrability argument uses the current null-measurability API;
- qualitative zero-mass and integrability proofs replace unused evaluated
  numerical mass bounds, as detailed below.

The initial 242-module version passed the full project Lake build.
Its post-rewrite audits, including the Sidon all-height width wrapper,
contain exactly `[propext, Classical.choice, Quot.sound]`.
The expanded 275-module version also passed the full project build
(4636 jobs), and its post-rewrite terminal audits give the same result.

Actual staged terminal audits for each of the following also contain
exactly those three principles:

- `ZetaVinogradovSummedZeroFree.exists_eventual_strip`;
- `ZetaEulerLineBound.bound_abs`;
- `UniformDirichletPowerBound.uniform_bound`;
- `FirstDerivativeTest.bound`;
- `RosserSchoenfeldExplicitFormula.finite_prime_explicitFormula`;
- `RosserSchoenfeldZeroMass.norm_square_mass_summable`;
- `analyticZetaZeroMultiplicity_conjugate`;
- `NontrivialZetaZero.im_ne_zero_of_eta_mass`.

The [kernel reference graph](rg-kernel-dependencies.json) records direct type
and proof-value references for all 3354 compiled constants across the
275-module project slice, including generated helpers. It has zero local
axioms and records the exact dependency boundary to mathlib.
No prohibited source shortcuts occur in the selected files.

## From the ordinate strip to the all-height zero-count interface

The Sidon wrapper takes \(C_0=1/10000<3\pi/10640\) and proves

    ∃ T₀ : ℝ,
      ZetaZeroFreeWidth (logarithmicZeroFreeWidth (1 / 20000)) T₀

The project width is the unshifted expression
\(C/((\log T)^{2/3}(\log\log T)^{1/3})\).
The conclusion covers every positive-height zero up to \(T\), with actual
analytic multiplicities.

1. Enlarge the source starting ordinate to \(U\ge e^2\).
   An actual zeta zero of height at least \(U\) is a member of the source
   subtype, since the omitted trivial zeros and the point \(1\) are real.
2. On positive ordinates, the source width is the project width at
   \(\gamma+2\). Both logarithmic factors are positive and increasing.
   For \(U\le\gamma\le T\), the width at \(\gamma+2\) is at least the
   width at \(T+2\).
3. For \(T\ge2\) and \(\log T\ge2\), \(T+2\le T^2\), so
   \(\log(T+2)\le2\log T\). Also
   \(\log\log(T+2)\le\log2+\log\log T\le2\log\log T\).
   Raising to powers \(2/3\) and \(1/3\) multiplies the denominator by
   at most \(2^{2/3}2^{1/3}=2\). Thus the shifted width dominates the
   unshifted width with coefficient \(C_0/2\).
4. The closed discrete zeta-zero set meets a compact disk in a finite set.
   Hence there are finitely many critical-strip zeros with
   \(0<\gamma\le U\). Each has \(\beta<1\), by nonvanishing on
   \(\Re s\ge1\). Since the project width tends to zero, it eventually
   lies below each of their finitely many positive margins \(1-\beta\).
5. Take the maximum of these thresholds. The two cases cover every zero
   occurrence up to \(T\). Repeating a zero by its multiplicity does not
   alter its real-part inequality.

These generic width estimates and the unconditional specialization are in
`Sidon/NumberTheory/ZetaZeroFree.lean`. Their full-project
dependency audits contain exactly the same three standard principles.

## Exact smoothed formula and qualitative mass

The additional terminal gives the literal arithmetic sum

\[
 \sum_{1\le n\le x}\Lambda(n)\log(x/n)
 =x-1-\log(2\pi)\log x-Z(\log x)+V(\log x),
\]

where

\[
 Z(t)=\sum_\rho m_\rho\frac{e^{\rho t}-1}{\rho^2},
 \qquad
 V(t)=\sum_{j\ge1}\frac{1-e^{-2jt}}{4j^2}.
\]

The exact formula's only premise is \(1\le x\). The zero sum contains
both ordinate signs and actual analytic multiplicities. Its printed
definition is an ordinary absolutely convergent `tsum`.
Gaussian formulas elsewhere in the source with an `hExplicit`
argument are not used.

The qualitative replacement avoids numerical verification of initial zeros.
Closedness of the zeta-zero set and \(\zeta(0)\ne0\) give
\(\epsilon>0\) such that \(\|\rho\|\ge\epsilon\) for every zero.
For \(0<\beta<1\), the reflected Poisson weight satisfies

\[
 P(\rho)=
 \frac{1-\beta}{(1-\beta)^2+\gamma^2}
 +\frac{\beta}{\beta^2+\gamma^2}
 \ge\frac1{1+\gamma^2}.
\]

Consequently

\[
 \frac{m_\rho}{\|\rho\|^2}
 \le\frac{1+\epsilon^2}{\epsilon^2}\,m_\rho P(\rho).
\]

The source's exact reflected logarithmic-derivative expansion makes
the nonnegative Poisson series summable. Comparison proves finite complete
reciprocal norm-square mass. That actual mass supplies the integrable
majorant for \(Z\); no evaluated numerical constant is required.
The statements of the exact transforms and explicit formula are unchanged.

The detailed proof, including all sum/integral exchanges and the
Fourier-injectivity argument, is in
[the log-smoothed formula note](log-smoothed-explicit-formula.md).
