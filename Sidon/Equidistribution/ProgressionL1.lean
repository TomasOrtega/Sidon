import Sidon.Equidistribution.Progressions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # A logarithmic `L¹` bound for progression Fourier sums -/

noncomputable section

open MeasureTheory

namespace Sidon

theorem circleHaar_eq_volume : circleHaar = (volume : Measure (AddCircle (1 : ℝ))) := by
  simpa only [ENNReal.ofReal_one, one_smul] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm

theorem integral_circleHaar_eq_interval (F : AddCircle (1 : ℝ) → ℝ) (a : ℝ) :
    (∫ α : AddCircle (1 : ℝ), F α ∂circleHaar) = ∫ t in a..a + 1, F t := by
  rw [circleHaar_eq_volume]
  exact (AddCircle.intervalIntegral_preimage 1 a F).symm

theorem fourier_neg_argument (n : ℤ) (α : AddCircle (1 : ℝ)) :
    fourier n (-α) = starRingEnd ℂ (fourier n α) := by
  rw [fourier_apply, smul_neg]
  exact fourier_neg'

theorem integral_even_bounded_inv_le (F : ℝ → ℝ) (hF : Continuous F)
    (heven : ∀ t, F (-t) = F t) (L : ℝ) (hL : 2 ≤ L)
    (hsmall : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), F t ≤ L)
    (hlarge : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), F t ≤ (2 * t)⁻¹) :
    (∫ t in -(1 / 2 : ℝ)..(1 / 2 : ℝ), F t) ≤ 2 + Real.log L := by
  let r : ℝ := L⁻¹
  have hLpos : 0 < L := by linarith
  have hr : 0 < r := inv_pos.mpr hLpos
  have hrhalf : r ≤ 1 / 2 := by
    dsimp [r]
    simpa only [one_div] using (inv_le_inv₀ hLpos (by norm_num : 0 < (2 : ℝ))).mpr hL
  have hnear : (∫ t in (0 : ℝ)..r, F t) ≤ 1 := by
    calc
      (∫ t in (0 : ℝ)..r, F t) ≤ ∫ _t in (0 : ℝ)..r, L := by
        apply intervalIntegral.integral_mono_on hr.le (hF.intervalIntegrable _ _)
          intervalIntegrable_const
        intro t ht
        exact hsmall t ⟨ht.1, ht.2.trans hrhalf⟩
      _ = 1 := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        exact inv_mul_cancel₀ hLpos.ne'
  have hinv : IntervalIntegrable (fun t : ℝ => (2 * t)⁻¹) volume r (1 / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro t ht
      rw [Set.uIcc_of_le hrhalf] at ht
      have : 0 < t := hr.trans_le ht.1
      positivity
    · exact (continuous_const.mul continuous_id).continuousOn
  have hfar : (∫ t in r..(1 / 2 : ℝ), F t) ≤ (1 / 2) * Real.log L := by
    calc
      (∫ t in r..(1 / 2 : ℝ), F t) ≤ ∫ t in r..(1 / 2 : ℝ), (2 * t)⁻¹ := by
        apply intervalIntegral.integral_mono_on hrhalf (hF.intervalIntegrable _ _) hinv
        intro t ht
        exact hlarge t ⟨hr.trans_le ht.1, ht.2⟩
      _ = (1 / 2) * Real.log ((1 / 2) / r) := by
        have heq : (fun t : ℝ => (2 * t)⁻¹) = fun t => (1 / 2) * t⁻¹ := by
          ext t
          simp [mul_comm]
        rw [heq, intervalIntegral.integral_const_mul, integral_inv_of_pos hr (by norm_num)]
      _ ≤ (1 / 2) * Real.log L := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.log_le_log (by positivity)
        dsimp [r]
        rw [div_inv_eq_mul]
        linarith
  have hhalf : (∫ t in (0 : ℝ)..(1 / 2 : ℝ), F t) ≤ 1 + (1 / 2) * Real.log L := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable 0 r) (hF.intervalIntegrable r (1 / 2))]
    exact add_le_add hnear hfar
  have hleft : (∫ t in -(1 / 2 : ℝ)..0, F t) =
      ∫ t in (0 : ℝ)..(1 / 2 : ℝ), F t := by
    have h := intervalIntegral.integral_comp_neg (f := F) (a := (0 : ℝ)) (b := 1 / 2)
    simpa only [heven, neg_zero] using h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (-(1 / 2)) 0) (hF.intervalIntegrable 0 (1 / 2)), hleft]
  linarith

theorem fourierL1_initialProgression_le (L : ℕ) (hL : 2 ≤ L) :
    fourierL1 (indicatorFinsupp (arithmeticProgression 0 1 L)) ≤ 2 + Real.log L := by
  let F : ℝ → ℝ := fun t =>
    ‖fourierSum (indicatorFinsupp (arithmeticProgression 0 1 L)) (t : AddCircle (1 : ℝ))‖
  have hcont : Continuous F :=
    (fourierSum _).continuous.norm.comp (AddCircle.continuous_mk' 1)
  have heven : ∀ t, F (-t) = F t := by
    intro t
    dsimp only [F]
    rw [show ((-t : ℝ) : AddCircle (1 : ℝ)) = -(t : AddCircle (1 : ℝ)) from
      QuotientAddGroup.mk_neg _ t]
    simp only [fourierSum_indicatorFinsupp_apply, fourier_neg_argument, ← map_sum,
      RCLike.norm_conj]
  have h := integral_even_bounded_inv_le F hcont heven L (by exact_mod_cast hL)
    (fun t _ => norm_fourierSum_arithmeticProgression_le_length 0 1 L (by norm_num) _)
    (fun t ht => norm_fourierSum_initialProgression_le_inv L t ht.1 ht.2)
  unfold fourierL1
  rw [integral_circleHaar_eq_interval _ (-(1 / 2))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  exact h

theorem norm_fourierSum_progression_eq_initial (a q : ℤ) (L : ℕ) (hq : q ≠ 0)
    (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (indicatorFinsupp (arithmeticProgression a q L)) α‖ =
      ‖fourierSum (indicatorFinsupp (arithmeticProgression 0 1 L)) (q • α)‖ := by
  rw [fourierSum_arithmeticProgression a q L hq,
    fourierSum_arithmeticProgression 0 1 L (by norm_num)]
  simp only [norm_mul, norm_fourier_apply, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_one, fourier_apply]

theorem fourierL1_progression_eq_initial (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    fourierL1 (indicatorFinsupp (arithmeticProgression a q L)) =
      fourierL1 (indicatorFinsupp (arithmeticProgression 0 1 L)) := by
  unfold fourierL1
  simp_rw [norm_fourierSum_progression_eq_initial a q L hq]
  have hmp : MeasurePreserving (fun α : AddCircle (1 : ℝ) => q • α) circleHaar circleHaar :=
    Measure.measurePreserving_zsmul circleHaar hq
  have h := integral_map (μ := circleHaar) hmp.measurable.aemeasurable
    (f := fun α : AddCircle (1 : ℝ) =>
      ‖fourierSum (indicatorFinsupp (arithmeticProgression 0 1 L)) α‖)
    ((fourierSum _).continuous.norm.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

theorem fourierL1_arithmeticProgression_le (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    fourierL1 (indicatorFinsupp (arithmeticProgression a q L)) ≤
      2 + Real.log (L + 1) := by
  rw [fourierL1_progression_eq_initial a q L hq]
  by_cases hL : 2 ≤ L
  · apply (fourierL1_initialProgression_le L hL).trans
    apply add_le_add le_rfl
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < L))
    linarith
  · have hcases : L = 0 ∨ L = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [fourierL1, arithmeticProgression, fourierSum_indicatorFinsupp_apply]
    · have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have heq : fourierL1 (indicatorFinsupp (arithmeticProgression 0 1 1)) = 1 := by
        simp [fourierL1, arithmeticProgression, fourierSum_indicatorFinsupp_apply]
      rw [heq]
      norm_num only [Nat.cast_one]
      linarith

end Sidon
