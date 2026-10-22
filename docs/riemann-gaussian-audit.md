# RiemannGaussian: semantic audit of the VK dependency

Audited source: [dbsanfte/RiemannGaussian at 6e969fd6e9c639eed280c595732248c106187603](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603).
The source pins Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
The relevant source files identify David Sanftenberg as author and copyright holder
and use Apache 2.0. The current Sidon worktree uses Lean/mathlib 4.35.0.

## Statements and definitions actually inspected

The main target is
[RiemannGaussian.ZetaVinogradovSummedZeroFree.exists_eventual_strip](https://github.com/dbsanfte/RiemannGaussian/blob/6e969fd6e9c639eed280c595732248c106187603/RiemannGaussian/ZetaVinogradovSummedZeroFree.lean).

Its nontrivial-zero type is the subtype of complex numbers satisfying

\[
 \zeta(s)=0,\qquad
 \neg\exists n:\mathbb N,\ s=-2(n+1),\qquad s\ne1.
\]

Here zeta is literally mathlib's riemannZeta, rather than a new surrogate function.
These definitions occur in GaussianZetaBridge.lean.
The ordinate scale is log(|t|+2), its level is log(log(|t|+2)), and

\[
 w(C,t)=
 \frac{C}{\log(|t|+2)^{2/3}\,
              \log\log(|t|+2)^{1/3}}.
\]

For every positive C below 3*pi/10640, the displayed theorem asserts
existence of a finite real T >= 4 such that every nontrivial zero rho
with |Im(rho)| >= T satisfies

\[
 w(C,\Im\rho)<\Re\rho<1-w(C,\Im\rho).
\]

The theorem has no zero-free, arithmetic cancellation, or density
assumption as an additional argument. The positive coefficient interval
is nonempty; the source proves that C=1/1150 belongs to it.
The following exists_eventual_nonvanishing theorem explicitly concludes
riemannZeta(s) != 0 for every point on or to the right of the corresponding
closed right edge. Its proof turns any hypothetical zero there into the
literal nontrivial-zero subtype. The ordinate threshold excludes both
trivial real zeros and the exceptional point 1.

This checks the semantics of the surface statement. It does not replace
compilation or a dependency audit of the imported proof.

## Analytic chain visible in source

ZetaVinogradovSummedCost.margin_of_budget calls the signed local
zero detector with actual analytic-disc and magnitude bounds at both t
and 2t. Its payment condition is subsequently discharged by an
eventual limit, rather than left as a premise of the final theorem.

ZetaVinogradovSummedBound.bound_strip bounds literal zeta by

\[
 |\zeta(\sigma+it)|
 \le1048576\,t^{g(n)}(\log t)^{2/3},
 \qquad
 g(n)=40\Delta_n^{3/2},\quad
 \Delta_n=\frac1{4096(2n+1)^2},
\]

on its stated near-one strip, above the explicit natural height
threshold at index 8n. The source retains the original finite Dirichlet
prefix, bounds all its dyadic blocks, and pays the Euler truncation
remainder. The moving natural degree and height feasibility are proved
in the schedule modules; the final starting height is finite but
unevaluated.

The selected proof path therefore requires genuine exponential-sum and
Vinogradov mean-value infrastructure as well as complex analysis.
Source inspection has not yet independently certified every step of that
arithmetic chain.

A search did not locate an Ingham zero-density theorem in the main
RiemannGaussian tree. The initially unlocated critical-line bound is
present under the generic name
`RiemannGaussian.ZetaEulerLineBound.bound_abs`.
Specializing its derivative index to `k = 1` gives

\[
 |\zeta(1/2+it)|\le8192\,|t|^{1/6}\log|t|
\]

above its explicit height threshold: the source proves
`DirichletPowerParameters.line 1 = 1/2` and
`DerivativePowerExponents.alpha 1 = 1/6`.
This theorem uses Euler truncation and finite derivative estimates directly.
It does not require an approximate functional equation as a separate input.
The applications agent is checking the specialization and the absorption
of the logarithm into a power exponent below one quarter.

## Dependency slicing and current verification boundary

The target module's custom import closure contains 1067 Lean modules
and 266100 source lines. Dropping the unused older cubic-region and
union comparison branch reduces this to 815 modules and 219777 lines.
The closure contains long historical chains: for example a
second-derivative Dirichlet bound imports hundreds of modules to access
the elementary polar identity for exp(-s*log(n)); finite eta blocks
similarly import a large analytic history for finite-sum definitions.

A provisional declaration-level slice selects 1507 declarations across
242 modules, about 21652 proof lines, preserving the public names and
separating private helpers by source module. The dependency graph is
acyclic. All selected files retain Apache attribution and immutable
source provenance. Option commands are excluded. Mathlib imports retain the original module
ancestry to avoid changing name resolution through an unrelated broad import.

This is a syntactic extraction, not yet a checked reuse result.
Lean compilation must resolve implicit, instance, namespace, and
attribute dependencies missed by source-token analysis. The terminal
theorem must then be checked with a kernel axiom audit before it can be
reported as an available Sidon dependency. No VK theorem or short-prime-
interval premise has been added to Sidon's checked public API on the
strength of this source audit alone.
