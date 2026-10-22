/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Topology.Algebra.Module.Cardinality
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Metric Set Topology
def riemannXi (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1

@[simp]
theorem riemannXi_zero : riemannXi 0 = -1 := by
  simp [riemannXi]

@[simp]
theorem riemannXi_one : riemannXi 1 = -1 := by
  simp [riemannXi]

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  apply Differentiable.sub
  · apply Differentiable.mul
    · apply Differentiable.mul
      · exact differentiable_id
      · exact (differentiable_const (c := (1 : ℂ))).sub differentiable_id
    · exact differentiable_completedZeta₀
  · exact differentiable_const (c := (1 : ℂ))

theorem analyticOnNhd_riemannXi :
    AnalyticOnNhd ℂ riemannXi Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_riemannXi

theorem analyticAt_riemannXi (s : ℂ) :
    AnalyticAt ℂ riemannXi s :=
  differentiable_riemannXi.analyticAt s

theorem riemannXi_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (1 - s) * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem isNontrivialZetaZero_of_riemannXi_eq_zero
    {s : ℂ} (hxi : riemannXi s = 0) :
    IsNontrivialZetaZero s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hxi
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
      mul_eq_zero] at hxi
    rcases hxi with hfactor | hcompleted
    · rcases mul_eq_zero.mp hfactor with hs | hs
      · exact (hs0 hs).elim
      · exact (hs1 (sub_eq_zero.mp hs).symm).elim
    · exact hcompleted
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]
  refine ⟨hzeta, ?_, hs1⟩
  rintro ⟨n, rfl⟩
  let w : ℂ := 1 - (-2 * ((n : ℂ) + 1))
  have hw0 : w ≠ 0 := by
    dsimp [w]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hpos : (0 : ℝ) < 1 + 2 * ((n : ℝ) + 1) := by positivity
    linarith
  have hwre : 1 ≤ w.re := by
    dsimp [w]
    norm_num
    positivity
  have hwcompleted : completedRiemannZeta w = 0 := by
    dsimp [w]
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hwzeta : riemannZeta w = 0 := by
    rw [riemannZeta_def_of_ne_zero hw0, hwcompleted, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re hwre hwzeta

theorem riemannXi_eq_zero_of_isNontrivialZetaZero
    {s : ℂ} (hs : IsNontrivialZetaZero s) :
    riemannXi s = 0 := by
  let ρ : NontrivialZetaZero := ⟨s, hs⟩
  rw [riemannXi_eq_mul_completedRiemannZeta
    (NontrivialZetaZero.coe_ne_zero ρ) hs.2.2,
    NontrivialZetaZero.completedRiemannZeta_eq_zero, mul_zero]

theorem riemannXi_eq_zero_iff_isNontrivialZetaZero (s : ℂ) :
    riemannXi s = 0 ↔ IsNontrivialZetaZero s :=
  ⟨isNontrivialZetaZero_of_riemannXi_eq_zero,
    riemannXi_eq_zero_of_isNontrivialZetaZero⟩

theorem analyticOrderAt_riemannXi_eq_riemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannXi ρ.1 =
      analyticOrderAt riemannZeta ρ.1 := by
  let factor : ℂ → ℂ := fun z => z * (1 - z)
  have hfactorAnalytic : AnalyticAt ℂ factor ρ.1 := by
    dsimp [factor]
    fun_prop
  have hfactorNe : factor ρ.1 ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (NontrivialZetaZero.coe_ne_zero ρ)
      (sub_ne_zero.mpr ρ.2.2.2.symm)
  have hfactorOrder : analyticOrderAt factor ρ.1 = 0 :=
    hfactorAnalytic.analyticOrderAt_eq_zero.mpr hfactorNe
  have heq :
      riemannXi =ᶠ[nhds ρ.1]
        fun z => factor z * completedRiemannZeta z := by
    filter_upwards
      [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ),
        eventually_ne_nhds ρ.2.2.2] with z hz0 hz1
    exact riemannXi_eq_mul_completedRiemannZeta hz0 hz1
  calc
    analyticOrderAt riemannXi ρ.1 =
        analyticOrderAt
          (fun z => factor z * completedRiemannZeta z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt factor ρ.1 +
        analyticOrderAt completedRiemannZeta ρ.1 :=
      analyticOrderAt_mul hfactorAnalytic
        (analyticAt_completedRiemannZeta_nontrivialZero ρ)
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hfactorOrder, zero_add]
    _ = analyticOrderAt riemannZeta ρ.1 :=
      (analyticOrderAt_riemannZeta_eq_completedRiemannZeta ρ).symm

theorem sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor
    {R : ℝ} (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ R) :
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) ≤
      ((∑ᶠ u, divisor riemannXi (closedBall 0 R) u : ℤ) : ℝ) := by
  classical
  let D := divisor riemannXi (closedBall (0 : ℂ) R)
  have hxiAnalytic :
      AnalyticOnNhd ℂ riemannXi (closedBall (0 : ℂ) R) :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  have hD (ρ : NontrivialZetaZero) (hρ : ρ ∈ S) :
      D ρ.1 = (analyticZetaZeroMultiplicity ρ : ℤ) := by
    have hmem : (ρ.1 : ℂ) ∈ closedBall (0 : ℂ) R := by
      simpa [mem_closedBall] using hS ρ hρ
    rw [show D ρ.1 = divisor riemannXi (closedBall (0 : ℂ) R) ρ.1 by rfl,
      hxiAnalytic.divisor_apply hmem,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
    rw [← Nat.cast_analyticOrderNatAt hfinite]
    simp [analyticZetaZeroMultiplicity]
  let T : Finset ℂ :=
    (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
  have himage : S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρS, rfl⟩
    rw [Set.Finite.mem_toFinset]
    change D ρ.1 ≠ 0
    rw [hD ρ hρS]
    exact Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive ρ))
  calc
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        ∑ z ∈ S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)),
          (D z : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ρ hρ
        rw [hD ρ hρ]
        norm_cast
      · intro ρ _ σ _ hρσ
        exact Subtype.ext hρσ
    _ ≤ ∑ z ∈ T, (D z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z _ _
      exact_mod_cast hxiAnalytic.divisor_nonneg z
    _ = ∑ᶠ z, (D z : ℝ) := by
      rw [finsum_eq_sum_of_support_subset]
      intro z hz
      change z ∈
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
      apply (D.finiteSupport
        (isCompact_closedBall (0 : ℂ) R)).mem_toFinset.mpr
      change D z ≠ 0
      intro hDz
      apply hz
      simp [hDz]
    _ = ((∑ᶠ z, D z : ℤ) : ℝ) := by
      exact (map_finsum (Int.castRingHom ℝ)
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R))).symm

end

end RiemannGaussian
