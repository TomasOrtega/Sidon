# Applications: proof and formalization plan

This file tracks Sections 3–5 and Appendices B–C of [Ortega–Prendiville, arXiv:2110.13447v1](https://arxiv.org/html/2110.13447). Expanded arguments are in `blueprint/src/chapters/applications.tex`. The result map below records compiled declarations. Existing `Sidon/Basic.lean` remains the source of the current checked Sidon definition.

Use finite integer sets for interval-supported functions, `AddCircle (1 : ℝ)` for the torus, Haar probability measure, and real functions for the dense-model vector spaces. Cast to complex numbers only inside Fourier transforms. Keep positive dimension and positive ambient length explicit. No proof may use `set_option` or `native_decide`.

## Results and file placement

| Paper result / blueprint label | Checked modules and declarations | Direct dependencies and status |
| --- | --- | --- |
| Lemma 3.2 / `app:progression-l1` | **Checked**, `Sidon/Equidistribution/ProgressionL1.lean`: `fourierL1_arithmeticProgression_le` | Geometric sums, the sine lower bound on `[0, π/2]`, Haar preservation under nonzero integer multiplication, integration of `min L (1 / dist θ 0)`. Replace `log \|P\|` by `log (2 + \|P\|)` to cover empty and singleton progressions. |
| Fourier test inequality / `app:progression-discrepancy` | **Checked**, `Sidon/Equidistribution/ProgressionEquidistribution.lean`: `progression_discrepancy_le_fourier_norm` | Fourier orthogonality, finite sum–integral interchange, progression–interval intersection. Establish this for arbitrary finite `S ⊆ [N]` first. |
| Theorem 3.1 / `app:progression-equidistribution` | **Checked**, same module: `sidon_progression_equidistribution`, `sidon_progression_equidistribution_log` | Previous inequality plus the main Fourier-uniformity theorem. Formalize an explicit `log (2+N)` inequality first; its `∀ ε > 0, ∃ Cε` power form is a corollary. |
| Corollaries 1.5, 1.6 / `app:interval-residue-corollaries` | **Checked**, `Sidon/Equidistribution/IntervalResidue.lean`: `sidon_interval_equidistribution`, `sidon_residue_equidistribution` | Integer endpoint rounding within 2, residue-class counts within 1 of `N/q`, `m ≥ √N/100 > 0`, and Theorem 3.1. Require `q > 0`, permit `q > N`, and specify arbitrary endpoint conventions. |
| Definition B.1 / `app:torus-fourier` | **Checked**, `Sidon/Analysis/TorusFourier.lean`: `torusHaar`, `torusFourierCoeff`, `torusCharacter` | Product Haar measure, finite products of circle characters. Avoid defining another competing Fourier transform on `ℤ`. |
| Kernel facts / `app:tensor-fejer` | **Checked**, `Sidon/Analysis/Approximation/Fejer.lean` and `Tensor.lean`: `tensorFejer`, `tensorFejer_nonneg`, `integral_tensorFejer`, `tensorFejer_eq_sum`, `integral_tensorFejer_tail_le` | Exact finite one-dimensional spectral expansion; Fubini and orthogonality; a global nonnegative domination proves the tail `d/(M*η²)`. The dimension factor is explicit. |
| Lemma 4.1, corrected / `app:trigonometric-approximation` | **Checked**, `Sidon/Analysis/Approximation/{Polynomial,Convolution,Uniform,Explicit}.lean`: `exists_trigonometric_approximation`, `ceil_fejer_bandwidth_le` | Produces real continuous values in `[0,1]`, error at most `ε`, a complex `Finsupp` coefficient family of modulus at most one, and support `\|n_i\|<M`. The checked recipe `M=ceil(27*d*K²/ε³)` works for every positive `ε` and positive dimension; the real ceiling bound `28*d*K²/ε³` assumes `ε≤1`. |
| Uniform-bandwidth obstruction / `app:no-uniform-bandwidth` | **Checked**, `Sidon/Analysis/Approximation/{Interpolation,SignedWeights,Counterexample}.lean`: `Sidon.BandwidthCounterexample.exists_continuous_dimension_obstruction`, `not_exists_uniform_dimension_bandwidth` | Ordinary complex Lagrange interpolation at `2M+1` explicit quarter-arc nodes reproduces frequencies `[-M,M]`; averaging with the conjugate relation gives real weights. Normalize their positive and negative parts into matching probability weights, tensor them, and test the Lipschitz maximum tent. At fixed `ε=1/16`, every finite coordinate bandwidth fails in some positive dimension. |
| Uniform smoothing / `app:compact-smoothing` | **Checked**, `Sidon/Equidistribution/TorusSmoothing.lean`: `exists_torus_smoothing`, `norm_torusTest_le_compact_smoothing` | Continuous bump autocorrelation and tensor products give compact support, Haar mass one, and absolutely summable Fourier coefficients with bound `(10/η)^d`. Exact Fourier convolution and uniform series reconstruction justify the test estimate. |
| Corollary 1.7 / `app:smooth-bohr` | **Checked**, `Sidon/Equidistribution/SmoothBohr.lean`: `sidon_smooth_equidistribution` | Compact smoothing, normalized discrepancy, and the main Fourier bound. The strong intermediate bound is `30*K^(d/(d+1))*(D/m)^(1/(d+1))`; the trivial bound `1` gives the paper’s exact exponents with an absolute constant. |
| Definition 1.9 / `app:regular-bohr` | **Checked**, `Sidon/Equidistribution/Bohr.lean`: `bohrSet`, `IsRegularBohrSet`, `isRegularBohrSet_iff_ratio` | Define regularity by the cross-multiplied cardinality inequality, so the definition makes sense for an empty set. Its equivalence with the paper's quotient definition assumes positive cardinality. |
| Cutoff / `app:bohr-cutoffs` | **Checked**, `Sidon/Equidistribution/Bohr.lean` and `BohrCutoffs.lean`: `clippedNormRamp`, `lipschitzWith_clippedNormRamp`, `bohr_discrepancy_le_cutoff_errors` | Maximum of coordinate distances is 1-Lipschitz; clipping to `[0,1]` is 1-Lipschitz. Using this direct maximum cutoff gives constant `1/t`, better than the paper's product bound `d/t`. |
| Corollary 1.11 / `app:regular-bohr-equidistribution` | **Checked**, `Sidon/Equidistribution/SmoothBohr.lean`: `sidon_regular_bohr_equidistribution` | Uniform smooth result plus regularity at `κ=±t/ρ`. Take `t = E^(3/(40d))`; if `t > ρ/(100d)`, use the trivial discrepancy bound. Handle `ρ ≥ 1/2` separately, where the discrepancy is zero. This also has the paper's absolute constant. |
| Lemma C.2 / `app:fourier-dual-norm`, `app:fourier-dual-properties` | **Checked**, `Sidon/Transference/FourierNorm.lean`: `Sidon.FourierSpace.dualNorm`, `abs_pairing_le`, `norm_realModulation_le`, `norm_mul_le`, `dualNorm_mul_le`, `abs_apply_le_dualNorm`, `dualNorm_one` | Haar inversion proves transform injectivity. Real modulation repairs the real/complex mismatch. Both algebra constants are exactly 1, and primal and dual closed unit balls are compact. |
| Lemma C.1 / `app:strict-separation` | **Checked**, `Sidon/Transference/DenseGeometry.lean`: `Sidon.FourierSpace.strict_separation` | Uses mathlib geometric Hahn–Banach and represents the continuous functional in coordinates. The colour simplex and its Fourier-ball thickening are compact and convex. |
| Polynomial approximation / `app:polynomial-max` | **Checked**, `Sidon/Transference/PolynomialMax.lean`: `Sidon.exists_polynomial_positiveMax`, `Sidon.FourierSpace.exists_dualNorm_aeval_bound` | Stone–Weierstrass on the fixed cube extracts an actual multivariate polynomial before `N` varies. Polynomial induction bounds its real Fourier dual norm uniformly in `N`. The explicit Bernstein recipe remains an independent informal witness. |
| Lemma 5.1 / `app:dense-model` | **Checked**, `Sidon/Transference/DenseModel.lean`: `Sidon.FourierSpace.colouring_dense_model`; integer adapter `Sidon.colouring_dense_model_interval` | All separation, polynomial, and real dual dependencies are closed. Nonmembership error is `7εN/8`; the separator is normalized to `(1+ε/2)N`. The normalized full-partition variant is `Sidon.colouring_dense_partition_model_interval`. |
| Solution count / `app:linear-count` | **Checked**, `Sidon/Transference/Counting.lean` and `IndicatorCounts.lean`: `linearSolutions`, `weightedSolutionCount`, `integral_prod_weightedFourier` | Finite products, zero extension, orthogonality. Count tuples with repeated coordinates, exactly as Theorem 1.15 does. |
| Quantitative FGR input / `app:fgr-dependency`, `qr:many-monochromatic` | **Checked**, `Sidon/Combinatorics/QuantitativeRado.lean`: `Sidon.QuantitativeRado.exists_many_monochromatic_linearSolutions` | Full proof from mathlib's checked Hales–Jewett theorem via finite Deuber extraction, an injective integer kernel matrix, a positive generator box, and bounded multiplicity. Returns the exact `linearSolutions` colour-class cardinal bound. Every reduction is compiled; see `docs/quantitative-rado-plan.md`. |
| Lemma 5.2 / `app:weighted-interval-count` | **Checked**, `Sidon/Combinatorics/QuantitativeRado/Weighted.lean`: `Sidon.QuantitativeRado.exists_many_weighted_linearSolutions` | Assign a colour with `g_i(x) ≥ 1/r`, then compare nonnegative products. Exact loss is `r^(-s)`. Nonnegativity and the pointwise sum-one condition are required only on `[N]`. |
| Exact energy / `app:sidon-energy` | `Sidon/Combinatorics/Energy.lean`: `IsSidonSet.addEnergy_eq`, `IsSidonSet.addEnergy_le` | **Checked declarations**: mathlib `Finset.addEnergy S S = 2*S.card^2-S.card` and its bound `≤ 2*S.card^2`. The displayed difference equation is equivalent to the sum-energy equation by rearrangement. |
| Fourth moment / `app:sidon-fourth-moment` | **Checked**, `Sidon/Transference/RestrictionMoments.lean` and `RestrictionBounds.lean`: `sidon_weighted_fourth_moment_le`, `sidon_restriction_moment_le`, `interval_restriction_moment_le` | Sidon majorant integer moments `p≥4` are bounded by `20000*N^(p−1)` under `m≥√N/100`; bounded dense moments `p≥2` by `N^(p−1)`. Uses exact finite orthogonality and the supremum bound. |
| Counting transfer / `app:counting-transfer` | **Checked**, `Sidon/Transference/CountingTransfer.lean`: `Sidon.sidon_counting_transfer` | Telescope the product and apply finite AM–GM to the `s−1` remaining maximum factors, then Haar-preserving coefficient dilation and moment bounds. Constant `40000*s`, with `s≥5`. |
| Theorem 1.15 / `app:partition-regularity` | **Checked**, `Sidon/PartitionRegularity.lean`: `Sidon.sidon_partition_regularity`, `sidon_partition_regularity_relative` | Complete dense models, checked quantitative Rado, counting transfer, normalized Sidon majorant, and asymptotic threshold are all assembled. Quantifier order is `∃ N₀≥1, γ>0, κ>0, ∀ N≥N₀, ∀ S, ∀ colouring`; conclusion is exact finite solution cardinality `≥κ*m^s/N`. |
| Proposition 1.13 / `app:odd-obstruction` | **Checked**, `Sidon/Constructions/Obstructions.lean` and `AsymptoticObstructions.lean`: `eventually_exists_sharp_odd_obstruction` | Affine preservation and parity, with a checked Bose–Chowla construction and the prime number theorem providing near-extremal cardinality for every sufficiently large ambient interval. |
| Remark 1.14 / `app:nonzero-sum-obstruction` | **Checked**, same modules: `exists_eventually_sharp_residue_obstruction` | Choose a prime not dividing the total coefficient sum, apply `p*S₀+1`, and supply `S₀` from the checked Bose–Chowla/PNT construction. The coefficient-dependent prime is fixed before the ambient length varies. |

## Corrections and proof boundaries

1. **Progression logarithm.** The printed `≪ log |P|` is false for a singleton and undefined at the empty progression. The uniform `log (2+|P|)` version repairs this without changing any asymptotic conclusion.
2. **Dimension factor in Appendix B, a counterexample to uniform bandwidth, and a repair for the applications.** The complement of a maximum-coordinate ball is a union of `d` coordinate bad sets. The displayed product Fejér estimate gives `d/(Mη²)`, so its proof yields bandwidth `ceil(27*d*K²/ε³)`. The stronger dimension-independent existence statement is **false when its implicit constant is absolute**: `app:no-uniform-bandwidth` supplies a full moment-matching counterexample for every finite bandwidth, at fixed `K=1` and `ε=1/16`. The missing union bound alone would not establish falsity; the separate counterexample does. **Both Bohr corollaries remain proved in full**, including absolute constants: compactly supported triangular smoothing has an absolutely summable infinite Fourier series and gives discrepancy `≤ 2Kη + R(10/η)^d`, with `R=D/m`. Optimization and the trivial bound 1 recover `K^(2/3)*E^(1/(8d))` with an absolute constant. No uniform finite bandwidth is needed.
3. **Real dual norm.** In C.2 the test vector `f e_α` is complex, although the norm dual was defined on real functions. The cosine argument in the blueprint fixes this and proves the exact stated algebra inequality.
4. **Colouring completion.** Lemma 5.1 supplies `Σg_i ≤ 1`, while Lemma 5.2 needs `Σg_i = 1`. The checked completion approximates all `r` colours, then adds the nonnegative deficit to the first colour. Normalization `Σν=N` bounds its mass by `r*τ*N`; starting with `τ=ε/(r+1)` preserves the prescribed final error. This works uniformly for every `r≥1`. The paper's displayed set identity at the end of Section 5 contains an indexing typo: its final coordinate should be `1 - Σ_{i<r} g_i`.
5. **Polynomial constants.** Stone–Weierstrass ensures existence, but a uniform argument must extract one fixed finite polynomial before varying `N` and the separator. The checked compact-cube evaluation-range proof does so directly; the explicit Bernstein recipe is another valid route. The constant monomial is retained, including degree zero.
6. **FGR quantitative theorem.** This dependency is now fully closed in Lean, including the bounded-weight consequence. The proof derives finite Deuber extraction from mathlib Hales–Jewett, constructs an injective integer kernel matrix with common positive leading entries, supplies a positive generator box, and counts finite-family fibers. It gives the exact `N^(s-1)` lower bound with finite constant choices and no external Ramsey or counting axiom.
7. **No distinctness claim.** The counted solution tuples can repeat coordinates. Do not relabel the theorem as a pairwise-distinct solution theorem without an additional argument.
8. **Construction existence.** The obstruction’s modular proof alone does not supply its near-extremal cardinality. The checked Bose–Chowla construction together with the prime number theorem now supplies that separate input; the proof does not infer existence from the Sidon upper bound or import the differently licensed Singer development.

## Checked dependency order

1. Fourier pairing, Haar orthogonality, interval indicators, and unique-difference energy.
2. Progression discrepancy and interval/residue rounding.
3. Tensor Fejér approximation, the uniform-bandwidth counterexample, and compact smoothing for both Bohr corollaries.
4. Real Fourier dual algebra, finite-dimensional separation, fixed compact-cube polynomial approximation, and dense models.
5. Hales–Jewett/Deuber quantitative Rado, weighted counting, counting transfer, and partition regularity.
6. Affine/modular obstructions, supplied with the independent Bose–Chowla/PNT asymptotic construction.

The checked final parameter recipe is: obtain weighted counting constant
`δ>0`; set `ε=min(1,δ/(80000*s))`; obtain `η>0` from the full-partition
dense model at this error; take `γ=min(1/2,η²/4096)` and enlarge the
threshold until `N^(-1/6)≤η²/4096`. The majorant Fourier norm is at most
`32*N*sqrt(deviation+N^(-1/6))≤η*N`. Counting transfer loses at most
`δ*N^(s−1)/2`, so the final finite solution cardinality constant is `κ=δ/2`.

### Checked Appendix C implementation

The Appendix C dependencies are now unconditional in Lean:

- `Sidon/Transference/FourierNorm.lean`: the `FourierSpace N` type carries
  the Fourier supremum norm. Haar orthogonality proves injectivity of its
  transform. The real dual is the operator norm of the coordinate pairing.
  Real phase modulation proves the constant-one algebra inequalities;
  coordinate bounds, definiteness, and compact primal and dual balls are checked.
- `Sidon/Transference/PolynomialMax.lean`: Stone–Weierstrass on the fixed
  compact cube yields an actual `MvPolynomial`; polynomial induction bounds
  its dual norm uniformly in the subsequently chosen interval length.
  The blueprint retains its independent explicit Bernstein proof.
- `Sidon/Transference/DenseGeometry.lean`: the colour simplex is compact
  and convex; every separating continuous linear functional is represented
  by coordinates; its positive maximum is realized by a simplex vertex.
- `Sidon/Transference/DenseModel.lean`: `FourierSpace.colouring_dense_model`
  proves the simultaneous colouring dense model with one positive parameter
  uniform in `N`, using normalized strict separation and the polynomial bound.
- `Sidon/Transference/DenseModelInterval.lean`: integer-interval adapters
  match the existing `weightedFourier` convention and zero-extend the models.
- `Sidon/Transference/DensePartition.lean`: a normalized partition of the
  majorant admits models whose pointwise sum is exactly one. Assigning the
  nonnegative deficit to the first colour costs at most `r+1` in the Fourier
  error; choosing the initial error smaller absorbs this factor.

The checked proof never applies a real dual functional to a complex test
function. Its key modulation uses `Re(z * character)` with `‖z‖=1`.
