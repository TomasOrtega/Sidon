/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace RiemannGaussian.PhaseIncrementInverse
noncomputable section

def rotation (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

def inverseStep (x : ℝ) : ℂ := (rotation x - 1)⁻¹

theorem norm_rotation (x : ℝ) : ‖rotation x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem rotation_add (x y : ℝ) : rotation (x + y) = rotation x * rotation y := by
  simp only [rotation, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem norm_rotation_sub_one (x : ℝ) :
    ‖rotation x - 1‖ = 2 * |Real.sin (x / 2)| := by
  rw [rotation, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem rotation_sub_one_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    rotation x - 1 ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotation_sub_one]
  have hs : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  positivity

private theorem inverseStep_two_mul (x : ℝ) (hx : Real.sin x ≠ 0) :
    inverseStep (2 * x) = ⟨-(1 / 2 : ℝ), -Real.cot x / 2⟩ := by
  unfold inverseStep
  apply inv_eq_of_mul_eq_one_right
  simp only [rotation, Complex.exp_ofReal_mul_I,
    Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.cot_eq_cos_div_sin]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero, sub_zero] <;>
    field_simp <;> nlinarith [Real.sin_sq_add_cos_sq x]

theorem inverseStep_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    inverseStep x = ⟨-(1 / 2 : ℝ), -Real.cot (x / 2) / 2⟩ := by
  have hs : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    inverseStep_two_mul (x / 2) hs

theorem inverseStep_re {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).re = -(1 / 2 : ℝ) := by
  rw [inverseStep_eq hx]

theorem inverseStep_im {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).im = -Real.cot (x / 2) / 2 := by
  rw [inverseStep_eq hx]

theorem cot_antitoneOn : AntitoneOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
    (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)).mpr
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy)
    (show y - x ≤ Real.pi by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hs
  nlinarith

theorem inverseStep_im_monotoneOn :
    MonotoneOn (fun x ↦ (inverseStep x).im) (Set.Ioo 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  change (inverseStep x).im ≤ (inverseStep y).im
  rw [inverseStep_im hx, inverseStep_im hy]
  have hc := cot_antitoneOn
    (show x / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hx.1, hx.2])
    (show y / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hy.1, hy.2])
    (show x / 2 ≤ y / 2 by linarith)
  linarith

theorem sin_half_lower {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) : η / Real.pi ≤ Real.sin (x / 2) := by
  by_cases hc : x ≤ Real.pi
  · have hs := Real.mul_le_sin (show 0 ≤ x / 2 by linarith [hx.1])
      (show x / 2 ≤ Real.pi / 2 by linarith)
    have he : 2 / Real.pi * (x / 2) = x / Real.pi := by ring
    rw [he] at hs
    exact (div_le_div_of_nonneg_right hx.1 Real.pi_pos.le).trans hs
  · have hs := Real.mul_le_sin (show 0 ≤ Real.pi - x / 2 by linarith [hx.2])
      (show Real.pi - x / 2 ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hs
    have hh : η / Real.pi ≤ 2 / Real.pi * (Real.pi - x / 2) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      field_simp
      linarith [hx.2]
    exact hh.trans hs

theorem norm_inverseStep_le {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) :
    ‖inverseStep x‖ ≤ Real.pi / (2 * η) := by
  have hs := sin_half_lower hη hx
  have hsp : 0 < Real.sin (x / 2) := lt_of_lt_of_le (div_pos hη Real.pi_pos) hs
  rw [inverseStep, norm_inv, norm_rotation_sub_one, abs_of_pos hsp]
  have hb := one_div_le_one_div_of_le (mul_pos (by norm_num : (0 : ℝ) < 2)
    (div_pos hη Real.pi_pos)) (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  calc
    (2 * Real.sin (x / 2))⁻¹ ≤ 1 / (2 * (η / Real.pi)) := by
      simpa only [one_div] using hb
    _ = Real.pi / (2 * η) := by field_simp

end
end RiemannGaussian.PhaseIncrementInverse
