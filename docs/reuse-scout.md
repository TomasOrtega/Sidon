# Reuse scout for arXiv:2110.13447

Audit date: 2026-10-22. Target: Miquel Ortega and Sean Prendiville,
*Extremal Sidon sets are Fourier uniform, with applications to partition
regularity*, especially the finite Fourier argument, Bohr-set
applications, partition regularity, and Appendices A–C.
[Paper](https://arxiv.org/html/2110.13447)

This is a source audit, not a claim that external projects were built in this
workspace. “Present” means a declaration or its `to_additive` source was read.
“Not found” describes the stated search scope; it does not establish global
nonexistence. The initial audit below records the original Lean `v4.14.0-rc2` /
mathlib `b17bf258da6542cd3a553ea33c03db938506ae92` checkout. The project now targets
the latest stable Lean/mathlib `v4.35.0`; the later migration audit records newly
reusable results. Historical immutable source links remain useful evidence.

## Latest stable migration: additional reuse

The upgraded project targets Lean/mathlib **v4.35.0**, mathlib commit
[`56a0058`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679).
The full Lean build passes. Documentation tooling versions and checks are
recorded in [the tooling audit](blueprint-upgrade-research.md).

- [`Analysis/Fourier/AddCircleMulti.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Fourier/AddCircleMulti.lean)
  supplies `UnitAddTorus.mFourier`, character density, the complete Fourier
  Hilbert basis, absolutely convergent inversion, and Parseval. The local
  `TorusFourier` module now consists of bridges preserving probability-Haar
  normalization; the earlier backported proofs were removed.
- [`NumberTheory/Chebyshev.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Chebyshev.lean)
  supplies the Chebyshev functions and their prime-power error estimates.
  [`NumberTheory/LSeries/ZetaZeros.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/LSeries/ZetaZeros.lean)
  supplies finiteness of bounded zeta zero sets. The local zero-counting and
  finite-layer modules account explicitly for analytic multiplicity.
- A proof-only Apache-licensed extraction from PNT+ now proves the weak prime
  number theorem, then `psi_isEquivalent`, `theta_isEquivalent`, and primes in
  every sufficiently large relative interval. This completes the sharp
  obstruction constructions. See [the source/port audit](pnt-port.md) and
  [third-party notices](../THIRD_PARTY_NOTICES.md). The dependency audit of the
  imported theorem reports only the three standard Lean axioms.
- This qualitative relative interval theorem does **not** imply the
  power-saving prime interval bound required for Corollary 1.4. The
  [quantitative research audit](prime-gap-research.md) and
  [expanded Ingham argument](ingham-prime-interval-proof.md) keep that
  remaining dependency explicit.

## Initial mathlib audit: directly available foundations

All paths in this table are relative to `Mathlib/` at the pinned revision.
Source links are immutable. Generated additive declarations are identified
from their `to_additive` annotations rather than from text search alone.

| Need | Existing file and declarations | What still needs a bridge |
| --- | --- | --- |
| Finitely supported functions on integers | [`Algebra/MonoidAlgebra/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Algebra/MonoidAlgebra/Defs.lean): `AddMonoidAlgebra`, `AddMonoidAlgebra.mul_def`, `AddMonoidAlgebra.mul_apply`, `AddMonoidAlgebra.mul_apply_antidiagonal`, `AddMonoidAlgebra.single_mul_single` | Multiplication is finite additive convolution. Define indicator finitely supported functions and prove the explicit `∑ y, f y * g (x-y)` presentation and support bounds used by the paper. |
| Finite sums and Cauchy–Schwarz | [`Algebra/Order/BigOperators/Ring/Finset.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean): `Finset.sum_mul_sq_le_sq_mul_sq`; [`Analysis/InnerProductSpace/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/InnerProductSpace/Basic.lean): `inner_sum`, `sum_inner`, `Finsupp.inner_sum` | Finite-support translation invariance and a complex-valued finite-sum norm-square inequality. These are short reusable steps in van der Corput, not the full differencing lemma. |
| Circle and distance to integers | [`Analysis/Normed/Group/AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/Normed/Group/AddCircle.lean): `AddCircle.norm_eq`, `AddCircle.norm_eq'`, `AddCircle.norm_le_half_period`, `UnitAddCircle.norm_eq` | At period one, `‖(x : UnitAddCircle)‖ = |x - round x|`. Use this existing quotient norm for the paper's distance-to-integers notation; do not invent a second quotient. Finite products can use `Fin d → UnitAddCircle`. |
| Positive-exponent Fourier characters | [`Analysis/Fourier/AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/Fourier/AddCircle.lean): `fourier`, `fourier_coe_apply`, `fourier_add`, `fourier_neg`, `fourier_apply`, `fourier_eval_zero`, `fourier_norm` | These declarations are in the root namespace: `namespace AddCircle` closes before `fourier`. `fourier n α` uses `exp(2πinα/T)`, matching the paper at `T=1`. Define the paper transform as the finite sum of coefficients times `fourier n α`; it is not the same object as `fourierCoeff`. |
| Haar probability and orthogonality | Same file: `AddCircle.haarAddCircle`, `orthonormal_fourier`, `fourierBasis`, `fourierCoeff`, `fourierCoeff_eq_intervalIntegral`, `tsum_sq_fourierCoeff` | Extract elementary finite character orthogonality, finite-polynomial Parseval, and the fourth-moment/additive-energy identity. The `fourierCoeff` definition uses the *negative* frequency. Record that sign explicitly. |
| Qualitative trigonometric approximation | Same file: `fourierSubalgebra_closure_eq_top`, `span_fourier_closure_eq_top`, `has_pointwise_sum_fourier_series_of_summable` | Stone–Weierstrass does not give Appendix B's explicit frequency cutoff, coefficient bounds, or Lipschitz approximation rate. Those quantitative statements remain work. |
| Finite cyclic Fourier transform | [`Analysis/Fourier/ZMod.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/Fourier/ZMod.lean): `ZMod.dft`, `ZMod.dft_apply`, `ZMod.dft_apply_zero`, `ZMod.invDFT_apply`, `ZMod.dft_dft`, `ZMod.dft_comp_neg` | Useful for an alternative cyclic embedding, but prove no wraparound for all required sums and reconcile signs/scaling. Direct integer finite sums avoid this extra embedding in Section 2. |
| Additive energy | [`Combinatorics/Additive/Energy.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Combinatorics/Additive/Energy.lean): `Finset.addEnergy`, `Finset.addEnergy_eq_card_filter`, `Finset.addEnergy_eq_sum_sq'`, `Finset.addEnergy_mono`, `Finset.card_sq_le_card_mul_addEnergy`, `Finset.le_card_add_mul_addEnergy` | Exact Sidon energy `2m²-m`, difference-fiber counts, and the Fourier fourth moment are not supplied by these general energy lemmas. |
| Hölder inequalities | [`MeasureTheory/Integral/MeanInequalities.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/MeasureTheory/Integral/MeanInequalities.lean): `ENNReal.lintegral_mul_le_Lp_mul_Lq`, `ENNReal.lintegral_mul_norm_pow_le`, `NNReal.lintegral_mul_le_Lp_mul_Lq` | Transfer the particular finite Fourier-polynomial integrals to this API and prove their integrability before applying the `L⁴` restriction/counting argument. The later `MeasureTheory/Function/Holder.lean` path does not exist at this pin. |
| Exponents and estimates | [`Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean): `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_mul`, `Real.rpow_le_rpow` | Explicit rounding and small-parameter cases for `H`, the error parameter, and degree cutoffs must be proved; the real-power API does not discharge them automatically. |
| Convex separation | [`Analysis/NormedSpace/HahnBanach/Separation.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Analysis/NormedSpace/HahnBanach/Separation.lean): `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_point_closed` | Available if a separation proof of a dense-model theorem is chosen. The paper's vector-valued model, quantitative Fourier norm, and bounded positive model must still be constructed. Separation alone is not Appendix C. |
| Finite coloring infrastructure | [`Combinatorics/HalesJewett.lean`](https://github.com/leanprover-community/mathlib4/blob/b17bf258da6542cd3a553ea33c03db938506ae92/Mathlib/Combinatorics/HalesJewett.lean): `Combinatorics.Line.exists_mono_in_high_dimension`, `Combinatorics.exists_mono_homothetic_copy` | This contains Hales–Jewett and a homothetic-copy consequence, not Rado's criterion for arbitrary coefficients or its quantitative many-solutions version. The file itself lists a finitary Van der Waerden version as future work. |

An all-source `rg` search of this pinned `Mathlib/` for Sidon, van der Corput,
Fejér/Fejer, additive Bohr neighborhoods, Varnavides, transference, and dense
models found no matching implementation of the paper's needed theorems.
Bohr–Mollerup hits concern the Gamma function and are irrelevant. Absence of
these words is not a substitute for the declaration audit above.

## Later mathlib: candidates to port selectively

The local Lean Pool dataset includes mathlib
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`, Lean `v4.34.0-rc1`.
Read-only inspection gives two especially relevant later additions:

* [`Combinatorics/Additive/Convolution.lean`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Combinatorics/Additive/Convolution.lean):
  `Finset.addConvolution`, `Finset.addConvolution_pos`,
  `Finset.addConvolution_eq_zero`, `Finset.addConvolution_le_card_left`,
  `Finset.addConvolution_le_card_right`, `Finset.addConvolution_neg`.
  This is a natural-number *representation count for two finsets*, not
  convolution of arbitrary complex weights. It is absent at the project pin.
* [`Analysis/Fourier/AddCircleMulti.lean`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean):
  `UnitAddTorus.mFourier`, `mFourier_add`, `mFourier_neg`,
  `mFourier_norm`, `mFourierCoeff`, `orthonormal_mFourier`,
  `mFourierSubalgebra_closure_eq_top`, `hasSum_sq_mFourierCoeff`.
  The product-character API is a useful reference for Appendix B, but it
  provides qualitative density rather than the required quantitative rate.

Neither later file is a current dependency. Port small needed facts with
their original attribution if appropriate; do not upgrade the entire project
just to obtain a representation count or a product of characters.

## Lean Pool

The intended archive is [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool),
as confirmed by its README and the local
`lean-pool-dataset/sources.toml`. The unrelated repository
`cabloo/lean-pool` appeared in broad repository search and is not used here.

The full locally available archive snapshot is
[`faa8c032722c955187fae103c96e8e93066f4592`](https://github.com/Vilin97/lean-pool/tree/faa8c032722c955187fae103c96e8e93066f4592),
Lean `v4.34.0-rc1`. The current README was also fetched; it describes a
maintained archive of independent completed projects rather than an integrated
mathlib replacement. Default-branch code searches for `Sidon`,
`vanDerCorput`, and `partition regular` returned no matching files. These
remote searches are nonresults, not a full audit of today's default branch.

Actual useful source in the local snapshot:

| File | Declarations read | Assessment |
| --- | --- | --- |
| [`LeanPool/KrafftSieve/Variance.lean`](https://github.com/Vilin97/lean-pool/blob/faa8c032722c955187fae103c96e8e93066f4592/LeanPool/KrafftSieve/Variance.lean) | `KrafftSieve.fHat`, `sum_exp_orthogonality`, `orthogonality_x`, `f_hat_normSq_expansion`, `parseval_standard`, `parseval_identity`, `f_hat_conj_symm` | Actual finite Fourier/Parseval proofs. Their transform is normalized by `1/q` and uses the negative exponent on `ZMod (q n)`; their functions are tied to a sieve construction. Reuse proof ideas or generalize the statements; they are not a drop-in API for the paper's integer transform. |
| [`LeanPool/OSforGFF/Bochner/FejerPD.lean`](https://github.com/Vilin97/lean-pool/blob/faa8c032722c955187fae103c96e8e93066f4592/LeanPool/OSforGFF/Bochner/FejerPD.lean) | `pd_l1_fourier_re_nonneg_theorem` | Actual nonnegativity theorem for Fourier transforms of continuous integrable positive-definite functions on a finite-dimensional real inner-product space. Its Fejér averaging uses overlapping real balls, not the discrete triangular kernel `μ_H` of this paper. |
| [`LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean`](https://github.com/Vilin97/lean-pool/blob/faa8c032722c955187fae103c96e8e93066f4592/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean) | `private theorem parseval_fin_fourier` | Actual finite-circle-polynomial Parseval proof using mathlib orthonormal characters. It is private and embedded in a large unrelated development, so extract a small general argument rather than import this file. |

No direct integer-Sidon Fourier-uniformity implementation was found in this
snapshot. The archive's candidate list mentions Singer's theorem, but a
candidate listing is not an accepted Lean Pool module.

## Tau Ceti

Read the canonical [TauCetiProject/TauCeti README](https://github.com/TauCetiProject/TauCeti/blob/main/README.md),
then inspected actual source at the code-search snapshot
[`8d89e8acfbca8b343e6449c3bf561c76f24ac072`](https://github.com/TauCetiProject/TauCeti/tree/8d89e8acfbca8b343e6449c3bf561c76f24ac072).
Its toolchain is `v4.36.0-rc1`; its manifest pins mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`. It is Apache-2.0, but has a
different and much newer dependency graph than this project.

* [`TauCeti/Analysis/Fourier/AddCircle.lean`](https://github.com/TauCetiProject/TauCeti/blob/8d89e8acfbca8b343e6449c3bf561c76f24ac072/TauCeti/Analysis/Fourier/AddCircle.lean)
  contains `TauCeti.fourier_injective`, `TauCeti.fourierAddChar`,
  `TauCeti.fourierAddChar_injective`, and
  `AddChar.exists_fourierAddChar_eq`. These classify and distinguish circle
  characters. The paper only needs explicit integer-indexed characters, so
  pinned mathlib already covers its immediate character needs.
* [`TauCeti/Analysis/Bochner/Herglotz.lean`](https://github.com/TauCetiProject/TauCeti/blob/8d89e8acfbca8b343e6449c3bf561c76f24ac072/TauCeti/Analysis/Bochner/Herglotz.lean)
  contains the public theorem
  `TauCeti.exists_isFiniteMeasure_integral_zpow_eq`. Its `fejerSum`,
  `fejerDensity`, and `fejerCount` helpers are private. The overlap-count
  bounds are conceptually useful, but they concern Herglotz representation
  and do not export the paper's finite-support Fejér probability kernel.

Remote code searches for `Sidon`, `Bohr`, and `vanDerCorput` returned no
matches. `Rado` found random graphs and Radon–Nikodym material, not partition
regularity. `partition regular` found unrelated graph-regularity partition
files. No direct reusable partition-regularity theorem was established by
these searches. Roadmaps and open issues were not counted as proved code.

## Other repositories with relevant actual code

### Singer's theorem and Sidon counting

[`d0d1/singer-theorem-lean`](https://github.com/d0d1/singer-theorem-lean/tree/0c890589afc58e8955a5d7c3a609daff6447da31)
at `0c890589afc58e8955a5d7c3a609daff6447da31` is particularly relevant.
The README and the following source files were fetched, not merely search
snippets. Its manifest pins mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`, Lean `v4.29.0`.

| File | Actual declarations | Relation to the paper |
| --- | --- | --- |
| [`Erdos30/Sidon.lean`](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/Sidon.lean) | `Erdos30.IsSidon`, `Erdos30.IsSidon.translate`, `Erdos30.isSidon_translate_iff` | Integer finset definition and translation invariance. Needs a proved equivalence to this project's generic set predicate. |
| [`Erdos30/AdditiveEnergy.lean`](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/AdditiveEnergy.lean) | `Erdos30.IsSidon.addEnergy_eq` | Exactly the finite combinatorial identity needed for the `L⁴` Fourier restriction estimate. |
| [`Erdos30/LindstromImproved.lean`](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/LindstromImproved.lean) | `Erdos30.IsSidon.shift_inter_le_one`, `johnson_numerical`, `sidon_intersection_sum_bound`, `sidon_johnson_bound`, `IsIntervalSidon.johnson_fourth_root`, `IsIntervalSidon.lindstrom_bound`, `sidonMaximum_le_lindstrom` | Close to Appendix A and the boundary estimate in Section 2. The final maximum bound is `⌊√N⌋ + ⌊√⌊√N⌋⌋ + 2` for `N ≥ 16`. |
| [`Erdos30/RepresentationL2.lean`](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/RepresentationL2.lean) | `Erdos30.sum_addConvolution_eq_card_sq`, `IsSidon.addConvolution_mem_one_two`, `IsSidon.sum_addConvolution_sq`, `IsSidon.sum_deficiency` | Actual representation-count `L¹/L²` identities, using later mathlib's `Finset.addConvolution`. |
| [`Erdos30/SingerTheorem.lean`](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/SingerTheorem.lean) | `Erdos30.Singer.singer_sidon_set`, `Erdos30.singerFamilyHypothesis_holds` | Actual prime-field Singer construction, relevant to the introductory extremal-size corollary. A quantitative prime-gap theorem is still needed for the paper's exponent. |

Reuse constraints: this repository is **GPL-3.0-only**. Its
`SingerTheorem.lean` contains a global `set_option maxHeartbeats`, and
`LindstromImproved.lean` contains a local one. No source is copied or imported
here. Any later adaptation must preserve applicable licensing and attribution
and produce proofs that build under this project's explicit ban on option
overrides and `native_decide`. README “zero-sorry” and build claims were not
independently established by building this external repository.

### Formal Conjectures

Local source at
[`6b3cde2dfd8700d039f34c2dcba48138fff473ac`](https://github.com/TomasOrtega/formal-conjectures/tree/6b3cde2dfd8700d039f34c2dcba48138fff473ac)
contains
[`FormalConjecturesForMathlib/Combinatorics/Basic.lean`](https://github.com/TomasOrtega/formal-conjectures/blob/6b3cde2dfd8700d039f34c2dcba48138fff473ac/FormalConjecturesForMathlib/Combinatorics/Basic.lean):
the global definition `IsSidon` expresses unordered-sum uniqueness by the two
ordered equalities. It also contains `Set.IsSidon.subset`,
`Set.IsSidon.insert`, and `Set.IsSidon.avoids_isAPOfLength_three`.
This is downstream code, **not mathlib**. It suggests a better elimination
interface than equality of two-element sets; prove equivalence before reuse.
The file includes unrelated conjecture infrastructure, so importing the whole
repository is unnecessary. Many problem files contain `sorry` statements;
their theorem names alone are not evidence of completed results.

The more recent
[`AItoBit/ma-tang-sidon-lean README`](https://github.com/AItoBit/ma-tang-sidon-lean/blob/5b60244934f6f220007f549ecff4e94bb5f2ee65/README.md)
also reports Sidon affine-invariance and finite gluing. Only its README was
read in this scout, so those are leads, not audited declarations. It
explicitly discloses an incomplete formalization of a different paper.

## Precise gap and placement plan

The following are **proposed modules**, not claims that their declarations
already exist. The main blueprint should track each proof separately.

1. `Sidon/Basic.lean`: generic Sidon predicate; equivalence of unordered sums
   and injective nonzero differences in additive commutative groups; subset
   and injective affine images. State cancellation hypotheses for any monoid
   formulation. This strong sum/difference equivalence does not require a
   torsion-free assumption; weaker distinct-summand Sidon variants differ.
2. `Sidon/Counting.lean`: off-diagonal difference fibers, exact energy,
   interval positive-difference counts, and the explicit Appendix A bound.
   These are the first candidates for a mathlib additive-combinatorics API.
3. `Sidon/FiniteFourier.lean`: finitely supported integer transform, positive
   phase convention, translation, reflection/conjugation, convolution,
   orthogonality, Parseval, and fourth moment. Target an eventual
   `Mathlib/Analysis/Fourier/Integer.lean` after the interface is stable.
4. `Sidon/Fejer.lean`: natural cutoff `H ≥ 1`, discrete triangular kernel,
   overlap-count formula, nonnegativity, total mass one, support, first-moment
   bounds, and weighted correlation identities. Natural cutoffs avoid
   repeated real-floor coercions in every later proof.
5. `Sidon/VanDerCorput.lean`: finite-support moving averages and the exact
   weighted differencing bound, including the reality/nonnegativity of its
   correlation sum. Then `Sidon/FourierUniformity.lean` supplies the four
   correlation estimates, boundary counts, choice of `H`, and all small-`N`
   cases. The uniformity theorem itself remains a project theorem.
6. `Sidon/Progressions.lean`: Fourier `L¹` bound for interval/progression
   indicators and their extraction from the uniformity theorem, keeping
   modulus positivity and endpoint conventions explicit.
7. `Sidon/TrigonometricApproximation.lean` and `Sidon/Bohr.lean`: product
   characters, quantitative Fejér/Jackson approximation, finite frequency
   count, regular Bohr-set smoothing, and the balancing choices. Qualitative
   Stone–Weierstrass does not fill these gaps.
8. `Sidon/Restriction.lean`, `Sidon/DenseModel.lean`,
   `Sidon/LinearConfigurations.lean`: `L⁴` restriction, dense bounded vector
   model, telescoping generalized von Neumann inequality, and removal of
   repeated-coordinate solutions. Their statements must fix all powers of
   `N` and all coefficient/dimension hypotheses.
9. `Sidon/PartitionRegularity.lean`: first the dense quantitative Rado result
   used as an external dependency in Section 5, then transference to extremal
   Sidon sets. Neither the nonzero coefficients nor the zero-sum subset
   hypothesis may be weakened to a different partition-regularity criterion.
10. `Sidon/ImprovedUniformity.lean`: Cilleruelo's local discrepancy estimate
    and the improved `N⁻¹/⁴` error. This is an additional substantial external
    dependency, not a consequence of the elementary Sidon cardinal bound.

The highest-risk missing pieces are quantitative Rado/counting, the bounded
vector dense model, quantitative torus approximation, and Cilleruelo's
discrepancy estimate. General analytic foundations exist, but no completed
drop-in Lean proof of these dependencies was established by this audit.
