# Applications: proof and formalization plan

This file tracks Sections 3–5 and Appendices B–C of [Ortega–Prendiville, arXiv:2110.13447v1](https://arxiv.org/html/2110.13447). Expanded arguments are in `blueprint/src/chapters/applications.tex`. Rows marked **Checked** describe compiled declarations; unmarked proposed names remain a roadmap. Existing `Sidon/Basic.lean` remains the source of the current checked Sidon definition.

Use finite integer sets for interval-supported functions, `AddCircle (1 : ℝ)` for the torus, Haar probability measure, and real functions for the dense-model vector spaces. Cast to complex numbers only inside Fourier transforms. Keep positive dimension and positive ambient length explicit. No proof may use `set_option` or `native_decide`.

## Results and file placement

| Paper result / blueprint label | Proposed file and declarations | Direct dependencies and status |
| --- | --- | --- |
| Lemma 3.2 / `app:progression-l1` | `Sidon/Analysis/Progression.lean`: `fourierIndicator_progression_l1_le` | Geometric sums, the sine lower bound on `[0, π/2]`, Haar preservation under nonzero integer multiplication, integration of `min L (1 / dist θ 0)`. Replace `log |P|` by `log (2 + |P|)` to cover empty and singleton progressions. |
| Fourier test inequality / `app:progression-discrepancy` | same: `progression_discrepancy_le_fourierNorm` | Fourier orthogonality, finite sum–integral interchange, progression–interval intersection. Establish this for arbitrary finite `S ⊆ [N]` first. |
| Theorem 3.1 / `app:progression-equidistribution` | same: `IsSidonSet.progression_discrepancy` | Previous inequality plus the main Fourier-uniformity theorem. Formalize an explicit `log (2+N)` inequality first; its `∀ ε > 0, ∃ Cε` power form is a corollary. |
| Corollaries 1.5, 1.6 / `app:interval-residue-corollaries` | `Sidon/Applications/Equidistribution.lean`: `IsSidonSet.interval_equidistribution`, `IsSidonSet.residue_equidistribution` | Integer endpoint rounding within 2, residue-class counts within 1 of `N/q`, `m ≥ √N/100 > 0`, and Theorem 3.1. Require `q > 0`, permit `q > N`, and specify arbitrary endpoint conventions. |
| Definition B.1 / `app:torus-fourier` | `Sidon/Analysis/Torus.lean`: `torusFourierCoeff`, `torusCharacter`, `torusMaxDist` | Product Haar measure, finite products of circle characters. Avoid defining another competing Fourier transform on `ℤ`. |
| Kernel facts / `app:tensor-fejer` | `Sidon/Analysis/TrigonometricApproximation.lean`: `tensorFejer`, `tensorFejer_nonneg`, `integral_tensorFejer`, `tensorFejer_eq_sum`, `integral_tensorFejer_compl_cube_le` | Expand the square of a geometric sum; count pairs with a prescribed difference; Fubini and orthogonality; finite union bound. The correct displayed tail here has a factor `d`. |
| Lemma 4.1, corrected / `app:trigonometric-approximation` | same: `exists_trigPolynomial_approx` | Tensor-kernel facts and a Lipschitz modulus. The proved recipe is `M = ceil (27*d*K^2/ε^3)` for `0 < ε ≤ 1`; choose zero polynomial for `ε ≥ 1`. An absolute bandwidth independent of dimension is impossible, as proved in the next row. |
| Uniform-bandwidth obstruction / `app:no-uniform-bandwidth` | `Sidon/Analysis/TrigonometricApproximation/Counterexample.lean`: `not_exists_uniform_dimension_bandwidth` | Real trigonometric interpolation at `2M+1` points outside radius `1/4`; split the resulting signed measure into two probability measures with matching low Fourier moments; tensor them; test the Lipschitz maximum bump. For `ε=1/16` and sufficiently large `d`, every rectangular-bandwidth-`M` polynomial fails uniform approximation. Full natural-language proof is supplied. |
| Uniform smoothing / `app:compact-smoothing` | `Sidon/Analysis/CompactSmoothing.lean`: `triangleKernel`, `fourierCoeff_triangleKernel`, `summable_fourierCoeff_triangleKernel`, `exists_smoothing_absSum_le` | Convolve two uniform arcs of length `η`; Fourier coefficients are `sinc²(π*n*η)` and their absolute sum is `≤ 10/η`. Tensor the kernels: support remains within max-distance `η`, while coefficient absolute sum is `≤ (10/η)^d`. Fourier uniqueness and absolute series convergence identify the kernel and its convolution. |
| Corollary 1.7 / `app:smooth-bohr` | `Sidon/Applications/Bohr.lean`: `IsSidonSet.smooth_bohr_equidistribution` | Compact smoothing and the main Fourier bound. Strong intermediate bound is `30*K^(d/(d+1))*(D/m)^(1/(d+1))`. Comparing it with the trivial bound 1 gives **the paper's exact exponents with an absolute constant**, independently of the unresolved uniform bandwidth of Lemma 4.1. |
| Definition 1.9 / `app:regular-bohr` | same: `bohrSet`, `IsRegularBohrSet` | Define regularity by the cross-multiplied cardinality inequality, so the definition makes sense for an empty set. Its equivalence with the paper's quotient definition assumes positive cardinality. |
| Cutoff / `app:bohr-cutoffs` | same: `bohrUpperCutoff`, `bohrLowerCutoff`, `lipschitzWith_bohrCutoff`, `bohrCutoff_sandwich` | Maximum of coordinate distances is 1-Lipschitz; clipping to `[0,1]` is 1-Lipschitz. Using this direct maximum cutoff gives constant `1/t`, better than the paper's product bound `d/t`. |
| Corollary 1.11 / `app:regular-bohr-equidistribution` | same: `IsSidonSet.regular_bohr_equidistribution` | Uniform smooth result plus regularity at `κ=±t/ρ`. Take `t = E^(3/(40d))`; if `t > ρ/(100d)`, use the trivial discrepancy bound. Handle `ρ ≥ 1/2` separately, where the discrepancy is zero. This also has the paper's absolute constant. |
| Lemma C.2 / `app:fourier-dual-norm`, `app:fourier-dual-properties` | **Checked**, `Sidon/Transference/FourierNorm.lean`: `Sidon.FourierSpace.dualNorm`, `abs_pairing_le`, `norm_realModulation_le`, `norm_mul_le`, `dualNorm_mul_le`, `abs_apply_le_dualNorm`, `dualNorm_one` | Haar inversion proves transform injectivity. Real modulation repairs the real/complex mismatch. Both algebra constants are exactly 1, and primal and dual closed unit balls are compact. |
| Lemma C.1 / `app:strict-separation` | **Checked**, `Sidon/Transference/DenseGeometry.lean`: `Sidon.FourierSpace.strict_separation` | Uses mathlib geometric Hahn–Banach and represents the continuous functional in coordinates. The colour simplex and its Fourier-ball thickening are compact and convex. |
| Polynomial approximation / `app:polynomial-max` | **Checked**, `Sidon/Transference/PolynomialMax.lean`: `Sidon.exists_polynomial_positiveMax`, `Sidon.FourierSpace.exists_dualNorm_aeval_bound` | Stone–Weierstrass on the fixed cube extracts an actual multivariate polynomial before `N` varies. Polynomial induction bounds its real Fourier dual norm uniformly in `N`. The explicit Bernstein recipe remains an independent informal witness. |
| Lemma 5.1 / `app:dense-model` | **Checked**, `Sidon/Transference/DenseModel.lean`: `Sidon.FourierSpace.colouring_dense_model`; integer adapter `Sidon.colouring_dense_model_interval` | All separation, polynomial, and real dual dependencies are closed. Nonmembership error is `7εN/8`; the separator is normalized to `(1+ε/2)N`. The normalized full-partition variant is `Sidon.colouring_dense_partition_model_interval`. |
| Solution count / `app:linear-count` | `Sidon/Applications/LinearEquation.lean`: `linearSolutionCount`, `linearSolutionCount_eq_integral`, `linearSolutionCount_smul`, `linearSolutionCount_telescope` | Finite products, zero extension, orthogonality. Count tuples with repeated coordinates, exactly as Theorem 1.15 does. |
| Quantitative FGR input / `app:fgr-dependency`, `qr:many-monochromatic` | **Checked**, `Sidon/Combinatorics/QuantitativeRado.lean`: `Sidon.QuantitativeRado.exists_many_monochromatic_linearSolutions` | Full proof from mathlib's checked Hales–Jewett theorem via finite Deuber extraction, an injective integer kernel matrix, a positive generator box, and bounded multiplicity. Returns the exact `linearSolutions` colour-class cardinal bound. Every reduction is compiled; see `docs/quantitative-rado-plan.md`. |
| Lemma 5.2 / `app:weighted-interval-count` | **Checked**, `Sidon/Combinatorics/QuantitativeRado/Weighted.lean`: `Sidon.QuantitativeRado.exists_many_weighted_linearSolutions` | Assign a colour with `g_i(x) ≥ 1/r`, then compare nonnegative products. Exact loss is `r^(-s)`. Nonnegativity and the pointwise sum-one condition are required only on `[N]`. |
| Exact energy / `app:sidon-energy` | `Sidon/Combinatorics/Energy.lean`: `IsSidonSet.addEnergy_eq`, `IsSidonSet.addEnergy_le` | **Checked declarations**: mathlib `Finset.addEnergy S S = 2*S.card^2-S.card` and its bound `≤ 2*S.card^2`. The displayed difference equation is equivalent to the sum-energy equation by rearrangement. |
| Fourth moment / `app:sidon-fourth-moment` | **Checked**, `Sidon/Transference/RestrictionMoments.lean` and `RestrictionBounds.lean`: `sidon_weighted_fourth_moment_le`, `sidon_restriction_moment_le`, `interval_restriction_moment_le` | Sidon majorant integer moments `p≥4` are bounded by `20000*N^(p−1)` under `m≥√N/100`; bounded dense moments `p≥2` by `N^(p−1)`. Uses exact finite orthogonality and the supremum bound. |
| Counting transfer / `app:counting-transfer` | **Checked**, `Sidon/Transference/CountingTransfer.lean`: `Sidon.sidon_counting_transfer` | Telescope the product and apply finite AM–GM to the `s−1` remaining maximum factors, then Haar-preserving coefficient dilation and moment bounds. Constant `40000*s`, with `s≥5`. |
| Theorem 1.15 / `app:partition-regularity` | **Checked**, `Sidon/PartitionRegularity.lean`: `Sidon.sidon_partition_regularity`, `sidon_partition_regularity_relative` | Complete dense models, checked quantitative Rado, counting transfer, normalized Sidon majorant, and asymptotic threshold are all assembled. Quantifier order is `∃ N₀≥1, γ>0, κ>0, ∀ N≥N₀, ∀ S, ∀ colouring`; conclusion is exact finite solution cardinality `≥κ*m^s/N`. |
| Proposition 1.13 / `app:odd-obstruction` | `Sidon/Applications/Obstructions.lean`: `IsSidonSet.affine_image`, `oddSet_no_four_sum_eq`, `exists_dense_sidon_without_four_sum_eq` | Elementary injective affine preservation and parity; asymptotic existence needs Singer-type near-extremal sets as a separate input. For `M=floor((N-1)/2)`, use `2*S₀+1`. |
| Remark 1.14 / `app:nonzero-sum-obstruction` | same: `exists_dense_sidon_without_eq_of_coeffSum_ne_zero` | Choose a fixed prime not dividing the total coefficient sum and use `p*S₀+1`. Again near-extremal existence is an explicit dependency. |

## Corrections and open proof obligations

1. **Progression logarithm.** The printed `≪ log |P|` is false for a singleton and undefined at the empty progression. The uniform `log (2+|P|)` version repairs this without changing any asymptotic conclusion.
2. **Dimension factor in Appendix B, a counterexample to uniform bandwidth, and a repair for the applications.** The complement of a maximum-coordinate ball is a union of `d` coordinate bad sets. The displayed product Fejér estimate gives `d/(Mη²)`, so its proof yields bandwidth `ceil(27*d*K²/ε³)`. The stronger dimension-independent existence statement is **false when its implicit constant is absolute**: `app:no-uniform-bandwidth` supplies a full moment-matching counterexample for every finite bandwidth, at fixed `K=1` and `ε=1/16`. The missing union bound alone would not establish falsity; the separate counterexample does. **Both Bohr corollaries remain proved in full**, including absolute constants: compactly supported triangular smoothing has an absolutely summable infinite Fourier series and gives discrepancy `≤ 2Kη + R(10/η)^d`, with `R=D/m`. Optimization and the trivial bound 1 recover `K^(2/3)*E^(1/(8d))` with an absolute constant. No uniform finite bandwidth is needed.
3. **Real dual norm.** In C.2 the test vector `f e_α` is complex, although the norm dual was defined on real functions. The cosine argument in the blueprint fixes this and proves the exact stated algebra inequality.
4. **Colouring completion.** Lemma 5.1 supplies `Σg_i ≤ 1`, while Lemma 5.2 needs `Σg_i = 1`. The checked completion approximates all `r` colours, then adds the nonnegative deficit to the first colour. Normalization `Σν=N` bounds its mass by `r*τ*N`; starting with `τ=ε/(r+1)` preserves the prescribed final error. This works uniformly for every `r≥1`. The paper's displayed set identity at the end of Section 5 contains an indexing typo: its final coordinate should be `1 - Σ_{i<r} g_i`.
5. **Polynomial constants.** Stone–Weierstrass ensures existence, but Lean still needs to extract one fixed finite polynomial before varying `N` and the separator. The checked compact-cube evaluation-range proof does so directly; the explicit Bernstein recipe is another valid route. The constant monomial is retained, including degree zero.
6. **FGR quantitative theorem.** This dependency is now fully closed in Lean, including the bounded-weight consequence. The proof derives finite Deuber extraction from mathlib Hales–Jewett, constructs an injective integer kernel matrix with common positive leading entries, supplies a positive generator box, and counts finite-family fibers. It gives the exact `N^(s-1)` lower bound with finite constant choices and no external Ramsey or counting axiom.
7. **No distinctness claim.** The counted solution tuples can repeat coordinates. Do not relabel the theorem as a pairwise-distinct solution theorem without an additional argument.
8. **Singer existence.** The obstruction's modular proof is complete independently of how `S₀` is supplied. Its near-extremal asymptotic cardinality is an additional construction theorem and must not be inferred from the upper bound for Sidon sets.

## Suggested implementation order

1. Build the common Fourier pairing/orthogonality API, real Fourier norm, interval indicators, and unique-difference energy identity.
2. Complete progressions and the interval/residue corollaries; these only require the main Fourier bound and elementary analysis.
3. Implement the corrected tensor Fejér approximation, its uniform-bandwidth counterexample, and the triangle-kernel smoothing alternative. The latter proves both Bohr corollaries with their exact absolute constants. Do not set the false uniform finite-bandwidth assertion of Lemma 4.1 as a Lean theorem target.
4. Implement the Fourier dual algebra, finite-dimensional separation bridge, Bernstein approximation, then the dense-model theorem.
5. Prove the quantitative FGR specialization, the weighted reduction, the counting-transfer inequality, and finally Theorem 1.15.
6. Implement elementary affine/modular obstructions, then attach the separate Singer/asymptotic existence input.

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
