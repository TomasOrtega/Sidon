module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
public import Mathlib.Analysis.Meromorphic.RCLike

@[expose] public section

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Metric Set Topology
open scoped Topology

theorem exists_riemannXiSphere_zeroFree
    {a b : ℝ} (hab : a < b) :
    ∃ R : ℝ, a < R ∧ R < b ∧
      ∀ z : ℂ, ‖z‖ = R → riemannXi z ≠ 0 := by
  let zeros : Set ℂ :=
    closedBall (0 : ℂ) b ∩ nontrivialZetaZeroSet
  have hzeros : zeros.Finite :=
    IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) b)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hinterval : (Ioo a b).Infinite := Set.Ioo_infinite hab
  have hnotSubset : ¬Ioo a b ⊆ (bad : Set ℝ) := by
    intro hsubset
    exact hinterval (bad.finite_toSet.subset hsubset)
  rcases Set.not_subset.mp hnotSubset with ⟨R, hR, hRbad⟩
  refine ⟨R, hR.1, hR.2, fun z hz hxi => ?_⟩
  apply hRbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, (riemannXi_eq_zero_iff_isNontrivialZetaZero z).mp hxi⟩
  rw [mem_closedBall, dist_zero_right, hz]
  exact hR.2.le

noncomputable def xiCanonicalRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_riemannXiSphere_zeroFree
    (show 4 * ((n : ℝ) + 3) < 4 * ((n : ℝ) + 3) + 1 by linarith))

theorem xiCanonicalRadius_spec (n : ℕ) :
    4 * ((n : ℝ) + 3) < xiCanonicalRadius n ∧
      xiCanonicalRadius n < 4 * ((n : ℝ) + 3) + 1 ∧
      ∀ z : ℂ, ‖z‖ = xiCanonicalRadius n → riemannXi z ≠ 0 :=
  Classical.choose_spec (exists_riemannXiSphere_zeroFree
    (show 4 * ((n : ℝ) + 3) < 4 * ((n : ℝ) + 3) + 1 by linarith))

theorem xiCanonicalRadius_pos (n : ℕ) : 0 < xiCanonicalRadius n :=
  (by positivity : 0 < 4 * ((n : ℝ) + 3)).trans
    (xiCanonicalRadius_spec n).1

theorem divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero (n : ℕ) :
    divisor riemannXi (sphere 0 (xiCanonicalRadius n)) = 0 := by
  classical
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) (xiCanonicalRadius n)
  · have hxi : riemannXi z ≠ 0 :=
      (xiCanonicalRadius_spec n).2.2 z
        (by simpa [mem_sphere, dist_zero_right] using hz)
    have horder : meromorphicOrderAt riemannXi z = 0 :=
      (analyticAt_riemannXi z).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
    rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hz]
    simp [horder]
  · change (if MeromorphicOn riemannXi
        (sphere 0 (xiCanonicalRadius n)) ∧
        z ∈ sphere 0 (xiCanonicalRadius n) then
          (meromorphicOrderAt riemannXi z).untop₀ else 0) = 0
    rw [ite_eq_right (fun h => hz h.2)]

theorem meromorphicOrderAt_riemannXi_ne_top (z : ℂ) :
    meromorphicOrderAt riemannXi z ≠ ⊤ := by
  have hmeromorphic : Meromorphic riemannXi :=
    meromorphicOn_univ.mp analyticOnNhd_riemannXi.meromorphicOn
  apply hmeromorphic.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  refine ⟨0, ?_⟩
  have horder : meromorphicOrderAt riemannXi 0 = 0 :=
    (analyticAt_riemannXi 0).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr (by simp)
  simp [horder]

theorem exists_riemannXiECanonicalDecomp (n : ℕ) :
    ∃ g : ℂ → ℂ,
      Complex.ECanonicalDecomp riemannXi g (xiCanonicalRadius n) := by
  apply MeromorphicOn.exists_ecanonicalDecomp
    (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn
  intro z
  exact meromorphicOrderAt_riemannXi_ne_top z

noncomputable def riemannXiCanonicalResidual (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_riemannXiECanonicalDecomp n)

theorem riemannXiCanonicalResidual_decomp (n : ℕ) :
    Complex.ECanonicalDecomp riemannXi
      (riemannXiCanonicalResidual n) (xiCanonicalRadius n) :=
  Classical.choose_spec (exists_riemannXiECanonicalDecomp n)

theorem norm_riemannXiCanonicalResidual_eq_on_sphere
    (n : ℕ) {z : ℂ} (hz : z ∈ sphere 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ = ‖riemannXi z‖ := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hxi : riemannXi z ≠ 0 :=
    (xiCanonicalRadius_spec n).2.2 z
      (by simpa [R, mem_sphere, dist_zero_right] using hz)
  have horder : meromorphicOrderAt riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    (sphere_subset_closedBall hz) horder hR
  have hcanonical (i : ℂ) :
      ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖ = 0 := by
    by_cases hi : divisor riemannXi (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor riemannXi (ball 0 R)).supportWithinDomain hi
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one himem hz,
        Real.log_one, mul_zero]
  have htrailing : meromorphicTrailingCoeffAt riemannXi z = riemannXi z :=
    (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi
  change Real.log ‖g z‖ = _ at hlog
  have hcanonicalSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) = 0 :=
    finsum_eq_zero_of_forall_eq_zero hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      exact divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  rw [hcanonicalSum, hsphereSum, htrailing] at hlog
  simp only [sub_zero, zero_add] at hlog
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((riemannXiCanonicalResidual_decomp n).ne_zero z
      (sphere_subset_closedBall hz))
  have hxipos : 0 < ‖riemannXi z‖ := norm_pos_iff.mpr hxi
  have hexp := congrArg Real.exp hlog
  simpa [Real.exp_log hgpos, Real.exp_log hxipos] using hexp

lemma norm_canonicalFactor_zero {R : ℝ} (hR : 0 < R) (i : ℂ) :
    ‖Complex.canonicalFactor R i 0‖ = R / ‖i‖ := by
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp [abs_of_pos hR]
  by_cases hi : ‖i‖ = 0
  · simp [hi]
  · field_simp

theorem one_le_norm_riemannXiCanonicalResidual_zero (n : ℕ) :
    1 ≤ ‖riemannXiCanonicalResidual n 0‖ := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
  have hxiAnalytic : AnalyticOnNhd ℂ riemannXi (ball 0 R) :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  have horder : meromorphicOrderAt riemannXi 0 = 0 :=
    (analyticAt_riemannXi 0).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr (by simp)
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    hzero horder hR
  have hcanonical (i : ℂ) :
      0 ≤ ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ := by
    by_cases hi : divisor riemannXi (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor riemannXi (ball 0 R)).supportWithinDomain hi
      have hine : i ≠ 0 := by
        intro hi0
        subst i
        apply hi
        rw [hxiAnalytic.meromorphicOn.divisor_apply]
        · simp [horder]
        · simpa [mem_ball, dist_zero_right] using hR
      have hinorm : ‖i‖ < R := by
        simpa [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hine)).mpr hinorm.le
      exact mul_nonneg (by
        exact_mod_cast hxiAnalytic.divisor_nonneg i) (Real.log_nonneg hfactor)
  have hcanonicalSum :
      0 ≤ (∑ᶠ i : ℂ,
        ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖) :=
    finsum_nonneg hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖0 - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      exact divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt riemannXi 0 = riemannXi 0 :=
    (analyticAt_riemannXi 0).meromorphicTrailingCoeffAt_of_ne_zero (by simp)
  change Real.log ‖g 0‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  have hlognonneg : 0 ≤ Real.log ‖g 0‖ := by
    rw [hlog]
    simpa using hcanonicalSum
  have hgpos : 0 < ‖g 0‖ := norm_pos_iff.mpr
    ((riemannXiCanonicalResidual_decomp n).ne_zero 0 hzero)
  exact (Real.log_nonneg_iff hgpos).mp hlognonneg

theorem exists_riemannXiCanonicalLog (n : ℕ) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      ∀ z ∈ ball 0 (xiCanonicalRadius n),
        HasDerivAt L (logDeriv (riemannXiCanonicalResidual n) z) z := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hdiff : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd z
      (ball_subset_closedBall hz)
    have hlog : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((riemannXiCanonicalResidual_decomp n).ne_zero z
          (ball_subset_closedBall hz))
    exact hlog.differentiableAt.differentiableWithinAt
  simpa [R, g] using hdiff.isExactOn_ball.with_val_at 0 0

noncomputable def riemannXiCanonicalLog (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_riemannXiCanonicalLog n)

@[simp] theorem riemannXiCanonicalLog_zero (n : ℕ) :
    riemannXiCanonicalLog n 0 = 0 :=
  (Classical.choose_spec (exists_riemannXiCanonicalLog n)).1

theorem riemannXiCanonicalLog_hasDerivAt
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    HasDerivAt (riemannXiCanonicalLog n)
      (logDeriv (riemannXiCanonicalResidual n) z) z :=
  (Classical.choose_spec (exists_riemannXiCanonicalLog n)).2 z hz

theorem exp_riemannXiCanonicalLog_mul_zero_eq
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    Complex.exp (riemannXiCanonicalLog n z) *
        riemannXiCanonicalResidual n 0 =
      riemannXiCanonicalResidual n z := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  let q : ℂ → ℂ := (fun w => Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := by
    exact mem_ball_self (by simpa [R] using xiCanonicalRadius_pos n)
  have hqdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := riemannXiCanonicalLog_hasDerivAt n (by simpa [R] using hw)
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    exact (by
      simpa [q, L, g] using
        (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt
          |>.differentiableWithinAt)
  have hqderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := riemannXiCanonicalLog_hasDerivAt n (by simpa [R] using hw)
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    have hqHas : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w +
          Complex.exp (-L w) * deriv g w) w := by
      simpa [q, L, g] using hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hqHas.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply]
    have hgne : g w ≠ 0 :=
      (riemannXiCanonicalResidual_decomp n).ne_zero w
        (ball_subset_closedBall (by simpa [R, g] using hw))
    rw [mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ hgne]
    ring
  have hqeq : q 0 = q z :=
    isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
      hqdiff hqderiv hzero (by simpa [R] using hz)
  have hg0eq : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, riemannXiCanonicalLog_zero] using hqeq
  change Complex.exp (L z) * g 0 = g z
  rw [hg0eq, ← mul_assoc, ← Complex.exp_add]
  simp

lemma logDeriv_finprod_zpow_apply_of_finite
    {ι : Type*} {F : ι → ℂ → ℂ} {d : ι → ℤ}
    (hd : (Function.support d).Finite) {z : ℂ}
    (hFne : ∀ i, d i ≠ 0 → F i z ≠ 0)
    (hFdiff : ∀ i, d i ≠ 0 → DifferentiableAt ℂ (F i) z) :
    logDeriv (∏ᶠ i, F i ^ d i) z =
      ∑ᶠ i, d i • logDeriv (F i) z := by
  classical
  have h₀ : ∏ᶠ i, F i ^ d i =
      ∏ i ∈ hd.toFinset, F i ^ d i :=
    finprod_eq_prod_of_mulSupport_subset _ <| by
      simp +contextual [Set.subset_def, not_imp_not]
  have hsub : Function.support (fun i ↦ d i • logDeriv (F i) z) ⊆
      hd.toFinset := by
    simp +contextual [-Function.support_mul, -mul_eq_zero,
      Set.subset_def, not_imp_not]
  calc
    logDeriv (∏ᶠ i, F i ^ d i) z =
        logDeriv (fun w ↦ ∏ i ∈ hd.toFinset, (F i ^ d i) w) z := by
      rw [h₀, Finset.prod_fn]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) z :=
      logDeriv_fun_prod (fun i hi ↦ zpow_ne_zero _ (hFne i (by simpa using hi)))
        (fun i hi ↦ (hFdiff i (by simpa using hi)).zpow
          (.inl (hFne i (by simpa using hi))))
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Pi.pow_def]
      simpa [zsmul_eq_mul] using
        logDeriv_fun_zpow (hFdiff i (by simpa using hi)) (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) z :=
      (finsum_eq_sum_of_support_subset _ hsub).symm

lemma logDeriv_canonicalFactor_eq
    {R : ℝ} (hR : 0 < R) {i z : ℂ}
    (hi : i ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzi : z ≠ i) :
    logDeriv (Complex.canonicalFactor R i) z =
      (-starRingEnd ℂ i) / ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * z) -
        1 / (z - i) := by
  have hfactor : Complex.canonicalFactor R i z ≠ 0 :=
    Complex.canonicalFactor_ne_zero hi hz hzi
  have hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ i) * z ≠ 0 := by
    rw [Complex.canonicalFactor_apply, div_ne_zero_iff] at hfactor
    exact hfactor.1
  have hden : (R : ℂ) * (z - i) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hR.ne'
    · exact sub_ne_zero.mpr hzi
  have hnumderiv :
      deriv (fun w : ℂ ↦ (R : ℂ) ^ 2 - (starRingEnd ℂ i) * w) z =
        -starRingEnd ℂ i := by
    rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
    simp
  have hdenderiv :
      deriv (fun w : ℂ ↦ (R : ℂ) * (w - i)) z = (R : ℂ) := by
    rw [deriv_const_mul_field, deriv_sub_const]
    simp
  rw [show Complex.canonicalFactor R i =
      fun w ↦ ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * w) /
        ((R : ℂ) * (w - i)) by rfl]
  rw [logDeriv_fun_div z hnum hden (by fun_prop) (by fun_prop)]
  simp only [logDeriv_apply]
  rw [hnumderiv, hdenderiv]
  field_simp [hR.ne', hzi]

lemma divisor_riemannXi_ball_eq_closedBall (n : ℕ) (z : ℂ) :
    divisor riemannXi (ball 0 (xiCanonicalRadius n)) z =
      divisor riemannXi (closedBall 0 (xiCanonicalRadius n)) z := by
  classical
  let R := xiCanonicalRadius n
  have hR : 0 < R := xiCanonicalRadius_pos n
  by_cases hb : z ∈ ball (0 : ℂ) R
  · rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hb,
      (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply
        (ball_subset_closedBall hb)]
  · by_cases hc : z ∈ closedBall (0 : ℂ) R
    · have hnorm : ‖z‖ = R := by
        rw [mem_ball, dist_zero_right] at hb
        rw [mem_closedBall, dist_zero_right] at hc
        exact le_antisymm hc (le_of_not_gt hb)
      have hxi : riemannXi z ≠ 0 :=
        (xiCanonicalRadius_spec n).2.2 z (by
          simpa [mem_sphere, dist_zero_right, R] using hnorm)
      have horder : meromorphicOrderAt riemannXi z = 0 :=
        (analyticAt_riemannXi z).meromorphicNFAt
          |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb,
        (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hc]
      simp [horder]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]

lemma riemannXi_eq_zero_of_divisor_ball_ne_zero
    {R : ℝ} {i : ℂ} (hi : divisor riemannXi (ball 0 R) i ≠ 0) :
    riemannXi i = 0 := by
  have himem : i ∈ ball (0 : ℂ) R :=
    (divisor riemannXi (ball 0 R)).supportWithinDomain hi
  by_contra hxi
  apply hi
  have horder : meromorphicOrderAt riemannXi i = 0 :=
    (analyticAt_riemannXi i).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply himem]
  simp [horder]

theorem logDeriv_riemannXi_eq_residual_sub_canonical_sum
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (xiCanonicalRadius n)) (hxi : riemannXi z ≠ 0) :
    logDeriv riemannXi z =
      logDeriv (riemannXiCanonicalResidual n) z -
        ∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
          logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) z := by
  classical
  let R := xiCanonicalRadius n
  let d : ℂ → ℤ := fun i => divisor riemannXi (ball 0 R) i
  let P : ℂ → ℂ := ∏ᶠ i, Complex.canonicalFactor R i ^ d i
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdFinite : (Function.support d).Finite := by
    simpa [d] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hmulSupport : (fun i =>
      Complex.canonicalFactor R i ^ d i).HasFiniteMulSupport := by
    apply Set.Finite.subset hdFinite
    intro i hi
    by_contra hdi
    have hdi0 : d i = 0 := by simpa [Function.mem_support] using hdi
    simp [hdi0] at hi
  have hzeroOfSupport {i : ℂ} (hi : d i ≠ 0) : riemannXi i = 0 :=
    riemannXi_eq_zero_of_divisor_ball_ne_zero (by simpa [d] using hi)
  have himem {i : ℂ} (hi : d i ≠ 0) : i ∈ ball (0 : ℂ) R :=
    (divisor riemannXi (ball 0 R)).supportWithinDomain (by simpa [d] using hi)
  have hzi {i : ℂ} (hi : d i ≠ 0) : z ≠ i := by
    intro h
    subst i
    exact hxi (hzeroOfSupport hi)
  have hfactorNe {i : ℂ} (hi : d i ≠ 0) :
      Complex.canonicalFactor R i z ≠ 0 :=
    Complex.canonicalFactor_ne_zero (himem hi)
      (ball_subset_closedBall (by simpa [R] using hz)) (hzi hi)
  have hfactorDiff {i : ℂ} (hi : d i ≠ 0) :
      DifferentiableAt ℂ (Complex.canonicalFactor R i) z :=
    (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).differentiableAt
  have hPAnalytic : AnalyticAt ℂ P z := by
    dsimp [P]
    apply analyticAt_finprod
    intro i
    by_cases hi : d i = 0
    · rw [hi]
      change AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z
      exact analyticAt_const
    · exact (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).zpow
        (hfactorNe hi)
  have hPne : P z ≠ 0 := by
    dsimp [P]
    apply finprod_apply_ne_zero
    intro i
    by_cases hi : d i = 0
    · simp [hi]
    · exact zpow_ne_zero _ (hfactorNe hi)
  have hfactorEq : g =ᶠ[nhds z] P * riemannXi := by
    have hball : ball (0 : ℂ) R ∈ nhds z :=
      isOpen_ball.mem_nhds (by simpa [R] using hz)
    have hxiNe : ∀ᶠ w in nhds z, riemannXi w ≠ 0 :=
      (analyticAt_riemannXi z).continuousAt.eventually_ne hxi
    filter_upwards [hball, hxiNe] with w hw hwxi
    have horder : meromorphicOrderAt riemannXi w = 0 :=
      (analyticAt_riemannXi w).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hwxi
    have heq := (riemannXiCanonicalResidual_decomp n)
      |>.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        (ball_subset_closedBall hw) horder hR
    have htrailing : meromorphicTrailingCoeffAt riemannXi w = riemannXi w :=
      (analyticAt_riemannXi w).meromorphicTrailingCoeffAt_of_ne_zero hwxi
    change g w = (P * riemannXi) w
    simpa [P, d, g, R,
      divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n,
      htrailing, finprod_apply hmulSupport] using heq
  have hproductLog :
      logDeriv P z = ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z := by
    dsimp [P]
    exact logDeriv_finprod_zpow_apply_of_finite hdFinite
      (fun i hi => hfactorNe hi) (fun i hi => hfactorDiff hi)
  have hmul := logDeriv_fun_mul (f := P) (g := riemannXi) z
    hPne hxi hPAnalytic.differentiableAt (differentiable_riemannXi z)
  have hlog : logDeriv g z = logDeriv P z + logDeriv riemannXi z := by
    rw [(logDeriv_congr_nhds hfactorEq).self_of_nhds]
    exact hmul
  rw [hproductLog] at hlog
  change logDeriv riemannXi z = logDeriv g z -
    ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z
  rw [hlog]
  ring

lemma norm_finsum_zsmul_le_of_nonneg
    {ι : Type*} {d : ι → ℤ} {f : ι → ℂ}
    (hd : (Function.support d).Finite)
    (hdnonneg : ∀ i, 0 ≤ d i) {C : ℝ}
    (hf : ∀ i, d i ≠ 0 → ‖f i‖ ≤ C) :
    ‖∑ᶠ i, d i • f i‖ ≤ ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
  classical
  have hsub : Function.support (fun i => d i • f i) ⊆ hd.toFinset := by
    intro i hi
    apply hd.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  calc
    ‖∑ i ∈ hd.toFinset, d i • f i‖ ≤
        ∑ i ∈ hd.toFinset, ‖d i • f i‖ := norm_sum_le _ _
    _ = ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * ‖f i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_zsmul ℂ]
      rw [Complex.norm_int_of_nonneg (hdnonneg i)]
    _ ≤ ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hdi : d i = 0
      · simp [hdi]
      · exact mul_le_mul_of_nonneg_left (hf i hdi) (by
          exact_mod_cast hdnonneg i)
    _ = (∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ = (∑ᶠ i, ((d i : ℤ) : ℝ)) * C := by
      congr 1
      symm
      exact finsum_eq_sum_of_support_subset _ (by
        intro i hi
        apply hd.mem_toFinset.mpr
        intro hdi
        apply hi
        simp [hdi])
    _ = ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
      congr 1
      exact (map_finsum (Int.castRingHom ℝ) hd).symm

end

end RiemannGaussian
