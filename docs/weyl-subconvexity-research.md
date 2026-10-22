# A sufficient weak subconvexity route

The remaining Ingham argument needs a critical-line bound with some fixed
exponent strictly below `1/4`. An unconditional Weyl theorem was found in
the generic balanced-line API of RiemannGaussian during this audit.
Its extracted proof closure is being checked before accepting it as a
project dependency. The independent weaker cancellation route below
also records a fallback and has a checked first-derivative component.
Only declarations explicitly identified as checked are project results.

## Source audit, 2026-10-22

The local mathlib v4.35.0 has the actual zeta functional equation, its
Dirichlet-series representation in the half-plane of absolute convergence,
Mellin transforms and inversion, Poisson summation, and Fourier-character
derivatives. Searches of its Lean sources found no approximate functional
equation, pointwise exponential-sum derivative test, exponent-pair
transformation, or zeta subconvexity theorem. A calculus second-derivative
test concerns local extrema and supplies no cancellation estimate.

[expdb](https://github.com/teorth/expdb/tree/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691)
has checked first-derivative oscillatory-integral estimates and
Euler–Maclaurin comparisons in
[`OscillatoryBounds.lean`](https://github.com/teorth/expdb/blob/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691/Expdb/ExponentialSums/OscillatoryBounds.lean).
Its finite-sum estimate assumes a small Euler–Maclaurin remainder,
including `K*T/N≤1`; it therefore cannot directly handle the critical
range `N≈sqrt T`. Its checked log-phase and scale-transfer modules are
useful calculus infrastructure. No checked A-process, B-process, second
derivative sum test, or zeta approximate functional equation appears in
the pinned tree. The
[contribution guide](https://github.com/teorth/expdb/blob/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691/CONTRIBUTING.md)
also distinguishes the limited Lean development from the larger blueprint.

Hiary's [primary paper](https://arxiv.org/html/1507.01261v4) gives a
classical derivative-test route to an explicit Weyl bound. Its Lemma 1.2
uses finite van der Corput differencing and a second derivative estimate;
Lemma 2.1 separately uses the Riemann–Siegel formula to shorten zeta to
Dirichlet polynomials of square-root length. These are separate analytic
prerequisites. We use the organization, but do not import its numerical
calculations or claim its estimates are already formalized.

## Actual Weyl theorem found in RiemannGaussian

The primary source
[`ZetaEulerLineBound.bound_abs`](https://github.com/dbsanfte/RiemannGaussian/blob/6e969fd6e9c639eed280c595732248c106187603/RiemannGaussian/ZetaEulerLineBound.lean#L119)
has no growth hypothesis: for `k≥1`, `Re s=line k`, and `|Im s|≥2`, it
bounds actual `riemannZeta s` by `8192*|Im s|^(alpha k)*log |Im s|`.
The definitions are `alpha k=1/(2^(k+2)-2)` and
`line k=1-(k+2)*alpha k`. Consequently `k=1` gives exactly `Re s=1/2`
and exponent `1/6`. Searching only for names containing “critical” or
“Weyl” missed this specialization.

Its proof uses a direct Euler truncation, complete dyadic blocks, and
the derivative estimates, rather than an approximate functional equation.
Source inspection does not establish successful compilation or an axiom
audit. Those checks remain prerequisites for accepting this theorem.

The elementary logarithm absorption is already checked in
`Sidon/NumberTheory/ZetaCriticalLine.lean`:
`sixth_rpow_mul_log_le_three_sixteenths` proves
`x^(1/6)*log x≤48*x^(3/16)` for every `x>0`.
The prospective specialization therefore gives the explicit constant
`8192*48=393216` at exponent `3/16`.

The bounded-height completion is also checked there. The critical-line
parameterization `zetaCriticalPoint t=1/2+i*t` never meets the pole, so
mathlib differentiability of actual zeta proves continuity of its
composition. Compactness of `[-2,2]` supplies one bound `B≥1`.
If the audited high-height estimate is accepted, take
`D=max(B,393216)`. At bounded height the factor `(1+|t|)^(3/16)` is at
least one; at larger height it dominates `|t|^(3/16)`. These two cases
give `(G_c)` for every real height, with no exceptional bounded interval.
The checked general completion lemma is
`exists_riemannZeta_criticalPoint_growth_of_tail`.

There is also a simple independent mathematical explanation for why
square-root-length truncation is unnecessary here. First Euler summation
at `X≈T²` has a bounded remainder and pole term on `Re s=1/2`. Strong
third derivative bounds control weighted blocks up to `T^(2/3)`;
second derivative bounds control blocks from there to `C*T`; and the
first derivative bound controls blocks `C*T≤N≤T²` by `sqrt N/T≤O(1)`.
Thus summing `O(log T)` blocks gives the Weyl estimate directly.
The extracted source uses a stronger Euler remainder, allowing a cutoff
comparable to `T` and eliminating the final long-block range entirely.

## A weaker cancellation estimate is enough

Let `e(x)=exp(2*pi*i*x)`. For a unit complex sequence with
`z_(k+1)=q_k*z_k`, put `a_k=(q_k-1)^(-1)`. Summation by parts gives

```
sum_(k=0)^n z_k
 = a_n*z_(n+1)-a_0*z_0
   -sum_(k=0)^(n-1) (a_(k+1)-a_k)*z_(k+1).
```

If `|q_k-1|≥gamma>0`, inverse subtraction gives
`|a_(k+1)-a_k|≤|q_(k+1)-q_k|/gamma²`. Therefore the sum has norm at most
`2/gamma + V/gamma²`, where `V` is the total variation of `q`.
For `q_k=e(delta_k)`, monotonicity and `delta_k∈[eta,1-eta]` imply
`V≤2*pi` and `gamma≥4*eta`. This proves the deliberately weak
first-derivative estimate `O(eta^(-2))` without cotangent monotonicity.

Suppose a real phase has second derivative of constant sign with
`lambda≤|f''|≤C*lambda`, where `0<lambda≤1`. Its consecutive phase
increments are monotone, with consecutive differences comparable to
`lambda`. Partition their values by their integer parts. There are at
most `O(lambda*L+1)` intervals. In each, remove increments whose distance
from an integer is below `eta`. Their total number is
`O((lambda*L+1)*(eta/lambda+1))`. Each remaining interval contributes
`O(eta^(-2))` by the preceding estimate. Thus

```
|sum e(f(n))| ≪ L*eta + eta/lambda
                 + (lambda*L+1)*(1+eta^(-2)).
```

Taking `eta=lambda^(1/3)/4` gives

```
|sum e(f(n))| ≪ L*lambda^(1/3)+lambda^(-2/3).
```

For the logarithmic phase on a subinterval of `[N,2N]`, the shift-`h`
difference has second derivative comparable to `h*T/N³`. The checked
Sidon van der Corput inequality then has the numerical form

```
|S|² ≪ N²/H + N*T^(1/3)*H^(1/3)
                 + N³*T^(-2/3)*H^(-2/3).
```

For `T^(1/3)≤N≤sqrt T`, choose an integer `H` comparable to
`N^(3/4)*T^(-1/4)`. This quantity is at least one and at most `N`;
also `H*T/N³≤1`, as required by the second derivative estimate. Division
by the weight normalization `N`, followed by taking square roots, gives

```
N^(-1/2)*|S|
 ≪ N^(1/8)*T^(1/8)+N^(3/4)*T^(-1/4)
 ≤ T^(3/16)+T^(1/8).
```

When `N<T^(1/3)`, the trivial weighted estimate `sqrt N` is at most
`T^(1/6)`. Partial summation handles the varying weight `n^(-1/2)`;
all initial subinterval sums need the same bounds. A dyadic decomposition
has `O(log T)` blocks, so the square-root-length Dirichlet polynomial is
`O(T^(3/16)*log T)`. A symmetric approximate functional equation is one
possible bridge to actual zeta. The stronger direct Euler route above
avoids that additional prerequisite when the sharper derivative tests
are available.

Finally `3/16<7/32<1/4`, so logarithmic domination gives the required
fixed power `c=7/32`. The density exponent becomes `A=2+4c=23/8`.
Choosing truncation power `tau=17/50` gives `A*tau=391/400<1` and
`1-tau=33/50<2/3`, leaving margins for both error terms.

## Formal implementation boundary

**Checked on Lean/mathlib v4.35.0:**
`Sidon/NumberTheory/ExponentialSums/FirstDerivative.lean` proves
`sum_mul_sub_next`, `norm_inv_sub_inv_le`,
`norm_sum_le_of_quotient_variation`, `norm_fourierChar_sub_le`,
`four_mul_le_norm_fourierChar_sub_one`,
`norm_sum_fourierChar_le_of_monotone_increments`, and
`norm_sum_fourierChar_le_quadratic_gap` in namespace
`Sidon.ExponentialSums`. The last theorem concerns the literal sum of
Fourier characters, under adjacent monotone increment and gap bounds.
For the independent weak route, the integer-strip partition, the second
derivative test, and its logarithmic phase application remain proof
obligations. Accepting the separately audited RiemannGaussian closure
would supply the stronger full chain. A functional equation alone does
not justify truncating zeta at square-root length.
