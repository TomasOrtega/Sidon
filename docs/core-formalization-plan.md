# Finite Fourier core: implementation plan and proof audit

This plan covers Sections 2 and 6 and Appendix A of [Ortega–Prendiville, arXiv:2110.13447](https://arxiv.org/abs/2110.13447). The detailed informal proof is [fourier-core.tex](../blueprint/src/chapters/fourier-core.tex). Proposed declaration names below describe future work; they are not a claim that these declarations currently exist.

The first implemented core module is `Sidon/Analysis/DiscreteFejer.lean`, checked with `lake env lean Sidon/Analysis/DiscreteFejer.lean`. Its declaration names are `Sidon.fejerWeight`, `fejerWeight_apply`, `fejerWeight_nonneg`, `sum_fejerWeight_mul`, `sum_fejerWeight_smul`, `sum_fejerWeight`, `fejerWeight_neg`, `fejerWeight_zero`, `fejerWeight_eq_zero_of_le_abs`, `abs_lt_of_mem_support_fejerWeight`, `sum_fejerWeight_mul_le`, `sum_fejerWeight_mul_abs_le`, and `sum_fejerWeight_mul_sqrt_abs_le`. It defines the difference distribution using `Finset.range H`, which has the same differences as `{1,…,H}`. The generic scalar-average identity works in every real module, including `ℂ`.

## Mathematical conventions

- `N : ℕ` with `hN : 0 < N`; `interval N := Finset.Icc (1 : ℤ) (N : ℤ)`.
- `S : Finset ℤ`, `hS : IsSidonSet (S : Set ℤ)`, and `hSN : S ⊆ interval N`.
- `m := (S.card : ℝ)`; convert to real before subtraction, multiplication, division, or square roots. Natural subtraction must not stand for a signed difference.
- `H : ℕ` with `hH : 0 < H`. The van der Corput lemma itself must permit every positive `H`. Only the boundary-error lemmas require `H ≤ N`.
- The frequency space is `AddCircle (1 : ℝ)`. Reuse the existing global declaration `fourier (T := 1) n : C(AddCircle 1, ℂ)` for `α ↦ exp (2πinα)`; do not redefine the quotient or exponential character.
- Use `ℤ →₀ ℂ` for general finitely supported functions. Define finite Fourier sums as bundled continuous maps so the existing continuous-map norm is the required supremum norm. Real finitely supported functions can be mapped to complex when needed.
- Prefer finite sums and explicit finite supports in the combinatorial core. Neither general measure-theoretic convolution nor the Fourier integral transform on locally compact vector spaces is necessary for Sections 2 and A.

## Suggested modules and declarations

The namespace should be `Sidon`. `Sidon/Basic.lean` already contains the global predicate `IsSidonSet`; migrate names only if doing so is justified by compatibility needs. Do not introduce a competing Sidon definition.

| File | Planned declarations | Mathematical contract |
| --- | --- | --- |
| `Sidon/Combinatorics/Differences.lean` | `IsSidonSet.eq_of_sub_eq_sub`, `IsSidonSet.iff_unique_nonzero_difference` | Cancellation plus unordered-pair equality gives uniqueness of nonzero differences; prove the converse once. |
| `Sidon/Combinatorics/Differences.lean` | `differenceCount`, `differenceCount_zero`, `IsSidonSet.differenceCount_eq_indicator` | Count `(x,y) ∈ S ×ˢ S` with `y - x = h`. At zero the result is `S.card`; off zero it is zero or one according to membership in the difference image. |
| `Sidon/Combinatorics/Intervals.lean` | `interval`, `card_interval`, `IsSidonSet.translate`, `IsSidonSet.inter` | Integer intervals, translation invariance, inherited Sidon property. Include the empty interval and length zero. |
| `Sidon/Analysis/FiniteFourier.lean` | `fourierSum`, `fourierSum_apply`, `fourierSum_add`, `fourierSum_sub`, `fourierSum_smul`, `norm_fourierSum_le_sum_norm` | A finite sum of bundled `fourier` characters; expose the evaluation formula and linearity. |
| `Sidon/Analysis/Correlation.lean` | `correlation`, `correlation_neg`, `correlation_zero`, `correlation_indicator`, `correlation_twist` | `correlation f g h = ∑ x, f x * conj (g (x+h))`; real part and conjugation identities with this fixed sign convention. |
| `Sidon/Analysis/DiscreteFejer.lean` | `fejerWeight`, `fejerWeight_eq_card`, `fejerWeight_eq_triangle`, `fejerWeight_nonneg`, `fejerWeight_neg`, `fejerWeight_zero`, `sum_fejerWeight`, `sum_fejerWeight_mul` | Define using pair fibres over the integer interval, normalize by `(H : ℝ)^2`; positivity hypotheses stay on lemmas, not hidden in total definitions. |
| `Sidon/Analysis/DiscreteFejer.lean` | `fejerWeight_eq_zero_of_le_abs`, `sum_fejerWeight_mul_abs_le`, `sum_fejerWeight_mul_sqrt_abs_le` | Support `|h| < H`, first moment at most `H`, square-root moment at most `√H`. |
| `Sidon/Analysis/VanDerCorput.lean` | `movingAverage`, `support_movingAverage_subset`, `sum_movingAverage`, `sum_sq_norm_movingAverage` | Support in `[1-H,N-1]`, mass preservation, and exact weighted correlation-energy identity. |
| `Sidon/Analysis/VanDerCorput.lean` | `norm_sum_sq_le_fejer_correlation`, `norm_fourierSum_sq_le_fejer_norm_correlation` | Real-valued right sides. The first uses `Complex.re`; the second bounds every frequency after multiplication by a unit character. |
| `Sidon/Combinatorics/IntervalSize.lean` | `le_add_sqrt_of_sq_le`, `IsSidonSet.card_le_sqrt_add_four_mul_rpow`, `IsSidonSet.card_le_five_mul_sqrt`, `IsSidonSet.card_inter_interval_le` | Explicit Appendix A bound `m ≤ √N + 4 N^(1/4)` and local coarse bound `5√L`. |
| `Sidon/Analysis/SidonCorrelation.lean` | `fejer_mass_nonzero_differences_ge`, `interval_overlap_card`, `boundaryInterval`, `card_boundaryInterval`, `mixedCorrelation_eq`, `selfCorrelation_error_le` | The exact mass inequality, boundary intervals of length `|h|`, mixed deficit, and the diagonal-aware error bound. |
| `Sidon/Analysis/PowerWindow.lean` | `floor_rpow_window_spec` | For `0 ≤ θ ≤ 1`, `floor(N^θ)` lies in `[1,N]` and between `N^θ/2` and `N^θ`. |
| `Sidon/FourierUniformity.lean` | `sidon_fourier_discrepancy_sq_le`, `sidon_fourier_uniformity` | Window-dependent estimate followed by the explicit constant `16` version of Theorem 1.2. |
| `Sidon/Combinatorics/WindowVariance.lean` | `windowCount`, `sum_windowCount`, `sum_sq_windowCount`, `windowVariance`, `windowVariance_eq`, `IsSidonSet.windowVariance_le`, `optimized_windowVariance_le` | Exact first and second moments; variance at `H = floor(N^(3/4))` has square root at most `3 N^(5/8) (1 + √λ N^(1/8))`. |
| `Sidon/Combinatorics/IntervalDiscrepancy.lean` | `expandedWindowInterval`, `contractedWindowInterval`, `sum_expanded_windowCount_ge`, `sum_contracted_windowCount_le`, `cilleruelo_interval_estimate` | Prove the full Cilleruelo-type interval theorem with absolute constant `11`, using the expanded interval for the upper bound and contracted interval for the lower bound. |
| `Sidon/ImprovedFourierUniformity.lean` | `cilleruelo_short_boundary`, `sidon_improved_fourier_uniformity` | Corollary 6.2 and Theorem 6.3, with squared constant `290 + 60*C`; the proved choice `C=11` gives `950`. |

The correlation and kernel modules can initially expose sums over explicit finite intervals. A later refactor can bundle kernels as `ℤ →₀ ℝ` if this makes rearrangement easier; do not maintain two independent convolution libraries. The chosen representation must make the hypotheses and finite support visible.

## Lemma statements to settle before implementation

The finite van der Corput theorem should have the following mathematical type, with all sums represented as finite-support sums:

```text
N > 0 → H > 0 → support f ⊆ interval N →
‖∑ x, f x‖² ≤ ((N : ℝ) + H) *
  ∑ h, fejerWeight H h * (correlation f f h).re
```

Do not state the inequality directly between complex numbers: Lean correctly has no compatible order on `ℂ`. First prove that the weighted correlation is exactly the nonnegative real moving-average energy. The Fourier version uses `‖correlation f f h‖` and is again a real inequality.

Fix `correlation f g h := ∑ x, f x * conj(g(x+h))`. Then the twist formula is multiplication by `fourier (-h) α`, and `C21(h) = C12(-h)` for real functions. Opposite sign conventions are harmless mathematically but mixing them will break expansion lemmas.

The discrepancy theorem should be stated first as a pointwise bound and then as a norm bound:

```text
∀ α : AddCircle 1,
  ‖fourierSum (indicator S) α -
    ((S.card : ℂ) / (N : ℂ)) * fourierSum (indicator (interval N)) α‖
  ≤ 16 * Real.sqrt N *
    Real.sqrt (|((S.card : ℝ) / Real.sqrt N) - 1| +
      (N : ℝ) ^ (-(1 / 6 : ℝ)))
```

Here `indicator S` is a finitely supported function with coefficients in `ℂ`; the `N` in `Real.sqrt N` is the real coercion. Use explicitly typed rational exponents, so `1/6` is never natural-number division. A reusable definition of the normalized deviation `δ` should return `ℝ`, not `ℂ` or `ℝ≥0∞`.

## Local mathlib reuse inspected

The following source declarations were inspected in the local checkout, rather than guessed from older mathlib versions:

- [`Mathlib/Analysis/Fourier/AddCircle.lean`](../.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean): global `fourier`, `fourier_apply`, `fourier_coe_apply`, `fourier_zero`, `fourier_neg`, `fourier_add`, `fourier_norm`; namespace `AddCircle` supplies `haarAddCircle`. In particular, the existing character declaration is global, not `AddCircle.fourier`.
- [`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`](../.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean): `Finset.sum_mul_sq_le_sq_mul_sq` is a finite Cauchy–Schwarz inequality. Apply it to nonnegative norms plus `norm_sum_le`, or reuse the inner-product version after checking its exact type.
- [`Mathlib/Analysis/Normed/Group/Basic.lean`](../.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean): `norm_sum_le`.
- [`Mathlib/Data/Int/Interval.lean`](../.lake/packages/mathlib/Mathlib/Data/Int/Interval.lean): `Int.card_Icc` and `Int.card_Icc_of_le`; the former gives the natural cardinality via `Int.toNat`, and the latter provides the convenient integer-cast cardinality when endpoints are ordered appropriately.
- [`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`](../.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean): `Real.rpow_add`, `Real.rpow_mul`, and their positivity variants support the exponent calculations.
- [`Mathlib/Algebra/MonoidAlgebra/Defs.lean`](../.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean): additive monoid algebra multiplication is already finitely supported convolution. This can be reused if convolution is needed beyond the direct finite-pair proof. Its existence does not by itself supply the specialized Fejér or van der Corput estimates.

The continuous Fourier series API and the discrete finite-support Fourier sum have different domains. Reuse the former's characters and continuous maps; a short bridge is required. No claim is made here that existing Parseval or inverse-transform lemmas have already been adapted to these finite sums.

## Audited gaps and edge cases

1. **Complex order in Lemma 2.1.** The paper writes a complex-valued correlation expression as the right side of a real inequality. Its weighted sum is real because it equals a sum of squared norms. The formal statement must expose that fact or take real parts.
2. **The zero shift in Theorem 1.2.** The off-zero Sidon identity fails at `h = 0`. The blueprint separately bounds the contribution by `m/H`, in addition to the `m/H` coming from captured mass. This explains the factor `2m/H` in the safe bound.
3. **Small real window parameters.** Work with positive integer windows and round once at optimization. For every `x ≥ 1`, `floor x ≥ x/2`; this prevents a denominator estimate from silently treating `floor H` as `H`.
4. **The Appendix A window restriction.** For integer `N≥1`, `N^(3/4)≤N` implies `ceil(N^(3/4))≤N` because `N` is already an integer upper bound. Thus no small-integer exception is needed. The moving-average argument in fact permits arbitrary positive `H`, which is a useful stronger statement.
5. **Empty local intervals.** The local bound at shift zero is `0 ≤ 5√0`; do not invoke a theorem requiring positive interval length there.
6. **Empty Sidon sets.** None of the baseline proof divides by `m`. `m=0` is therefore included throughout. Later average statements that divide by `|S|` will need their own nonemptiness hypothesis.
7. **Positive ambient interval length.** Quantitative normalized statements require `N>0`. For `N=0`, the underlying finite Fourier sum is zero, but expressions involving division and negative powers should not be used to encode the intended analytic estimate.
8. **Square-root linearization.** `|m²/N - 1| ≤ 6δ` uses the separately proved `m ≤ 5√N`, not an unstated assumption that the Sidon set is extremal.
9. **Cilleruelo's theorem requires a separate proof.** The source explicitly imports it. The blueprint now supplies a full proof using the finite variance identity from [Cilleruelo's primary paper](https://math.colgate.edu/~integers/a11/a11.pdf), with a contracted-window lower bound. The implementation must prove those lemmas before using the interval theorem; the source attribution is not a substitute for a Lean proof. The subsequent short-boundary corollary also requires the main term `Lm/N ≤ 5N^(1/4)`.
10. **The last mixed error in Section 6.** The missing bookkeeping step is `√δ N^(7/8) ≤ (Nδ + N^(3/4))/2`. This is the arithmetic–geometric mean inequality with both nonnegative factors written explicitly.

## Build-preserving implementation order

1. Establish difference uniqueness and interval combinatorics, importing only the existing basic file and finite-set interval APIs.
2. Add the character-sum bridge, kernel identities, and moving-average identity as independent reusable lemmas.
3. Prove van der Corput with no restriction `H ≤ N`; derive Appendix A and its local coarse corollary.
4. Prove the three error bounds separately, then assemble the window-dependent estimate. Keep the arithmetic constant calculation separate from finite-sum rearrangement.
5. Add the floor-power lemma and derive the baseline norm estimate.
6. Prove the window-variance identity and the expanded/contracted-window discrepancy estimates, then the full Cilleruelo-type interval theorem and improved Fourier bound. The informal proof supplies every mathematical step; Lean declarations remain pending until compiled.

Each completed lemma should be compiled before downstream modules import it. Keep the root import list buildable throughout. Use no `set_option`, `set_options`, `native_decide`, or proof placeholders. The blueprint should receive `\leanok` only after the corresponding declaration has been checked by the Lean kernel.
