module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section

/-! # Integrating circle averages through vertical slices -/

noncomputable section

open Set MeasureTheory Complex Real

namespace Sidon

theorem setIntegral_translate_Icc (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (v : ℝ) :
    (∫ y in Icc a b, f (y + v)) = ∫ t in Icc (a + v) (b + v), f t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_add_right]
  rw [intervalIntegral.integral_of_le (show a + v ≤ b + v by linarith),
    ← integral_Icc_eq_integral_Ioc]

theorem integral_angularAverage_le {a b L : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc 0 (2 * π)))
    (hslice : ∀ θ ∈ Icc 0 (2 * π), (∫ y in Icc a b, f y θ) ≤ L) :
    (∫ y in Icc a b, (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), f y θ) ≤ L := by
  have hi : Integrable f.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [integral_const_mul, integral_integral_swap hi]
  calc
    _ ≤ (2 * π)⁻¹ * ∫ _ in Icc 0 (2 * π), L := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_on hi.integral_prod_right (integrable_const _)
        measurableSet_Icc hslice
    _ = L := by
      simp [mul_assoc, max_eq_left (by positivity : (0 : ℝ) ≤ 2 * π)]

def verticalCircleRectangle (R T : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (2 - R) (2 + R) ∧ z.im ∈ Icc 1 (T + 3)}

theorem circleMap_vertical_center (y R θ : ℝ) :
    circleMap (2 + (y : ℂ) * I) R θ =
      ((2 + (circleMap 0 R θ).re : ℝ) : ℂ) +
        ((y + (circleMap 0 R θ).im : ℝ) : ℂ) * I := by
  have hh : circleMap (2 + (y : ℂ) * I) R θ =
      (2 + (y : ℂ) * I) + circleMap 0 R θ := by simp [circleMap, add_assoc]
  rw [hh]
  apply Complex.ext <;> simp

theorem circleMap_vertical_mem_rectangle {R T y : ℝ} (hR : 0 ≤ R)
    (hR1 : R ≤ 3 / 2) (hy : y ∈ Icc 3 (T + 1)) (θ : ℝ) :
    circleMap (2 + (y : ℂ) * I) R θ ∈ verticalCircleRectangle R T := by
  have hre := Complex.abs_re_le_norm (circleMap 0 R θ)
  have him := Complex.abs_im_le_norm (circleMap 0 R θ)
  rw [norm_circleMap_zero, abs_of_nonneg hR] at hre him
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hre
  obtain ⟨hilo, hihi⟩ := abs_le.mp him
  rw [circleMap_vertical_center]
  have hh : (2 + (circleMap 0 R θ).re ∈ Icc (2 - R) (2 + R)) ∧
      (y + (circleMap 0 R θ).im ∈ Icc 1 (T + 3)) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  simpa [verticalCircleRectangle] using hh

theorem integrableOn_circleAverage_vertical {F : ℂ → ℝ} {R T : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2)
    (hF : ContinuousOn F (verticalCircleRectangle R T)) :
    IntegrableOn (fun y : ℝ => circleAverage F (2 + (y : ℂ) * I) R)
      (Icc 3 (T + 1)) := by
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      (Icc 3 (T + 1) ×ˢ Icc 0 (2 * π)) := by
    apply hF.comp
    · unfold circleMap
      fun_prop
    · intro p hp
      exact circleMap_vertical_mem_rectangle hR hR1 hp.1 p.2
  have hi : Integrable
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      ((volume.restrict (Icc 3 (T + 1))).prod (volume.restrict (Icc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    ← integral_Icc_eq_integral_Ioc]
  exact hi.integral_prod_left.const_mul _

/-- Vertical integration of a circle average costs no extra constant. -/
theorem integral_circleAverage_vertical_le {F : ℂ → ℝ} {R T L : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2) (hT : 3 ≤ T)
    (hF : ContinuousOn F (verticalCircleRectangle R T))
    (hF0 : ∀ z ∈ verticalCircleRectangle R T, 0 ≤ F z)
    (hslice : ∀ u ∈ Icc (2 - R) (2 + R),
      (∫ t in Icc 1 (T + 3), F ((u : ℂ) + (t : ℂ) * I)) ≤ L) :
    (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * I) R) ≤ L := by
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      (Icc 3 (T + 1) ×ˢ Icc 0 (2 * π)) := by
    apply hF.comp
    · unfold circleMap
      fun_prop
    · intro p hp
      exact circleMap_vertical_mem_rectangle hR hR1 hp.1 p.2
  simp_rw [circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_angularAverage_le
    (f := fun y θ => F (circleMap (2 + (y : ℂ) * I) R θ)) hc
  intro θ _
  let u : ℝ := 2 + (circleMap 0 R θ).re
  let v : ℝ := (circleMap 0 R θ).im
  have hre := Complex.abs_re_le_norm (circleMap 0 R θ)
  have him := Complex.abs_im_le_norm (circleMap 0 R θ)
  rw [norm_circleMap_zero, abs_of_nonneg hR] at hre him
  have hu : u ∈ Icc (2 - R) (2 + R) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hre
    exact ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
  have hv : -R ≤ v ∧ v ≤ R := abs_le.mp him
  have hi : IntegrableOn (fun t : ℝ => F ((u : ℂ) + (t : ℂ) * I))
      (Icc 1 (T + 3)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply hF.comp (by fun_prop)
    intro t ht
    exact ⟨by simpa using hu, by simpa using ht⟩
  have hsub : Icc (3 + v) (T + 1 + v) ⊆ Icc 1 (T + 3) := by
    apply Icc_subset_Icc <;> linarith [hv.1, hv.2]
  calc
    _ = ∫ y in Icc 3 (T + 1), F ((u : ℂ) + ((y + v : ℝ) : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [circleMap_vertical_center]
    _ = ∫ t in Icc (3 + v) (T + 1 + v), F ((u : ℂ) + (t : ℂ) * I) :=
      setIntegral_translate_Icc (fun t => F ((u : ℂ) + (t : ℂ) * I))
        (a := 3) (b := T + 1) (by linarith) v
    _ ≤ ∫ t in Icc 1 (T + 3), F ((u : ℂ) + (t : ℂ) * I) := by
      apply setIntegral_mono_set hi _ hsub.eventuallySubset
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hF0 _ ⟨by simpa using hu, by simpa using ht⟩
    _ ≤ L := hslice u hu

end Sidon
