module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

@[expose] public section

namespace RiemannGaussian.ZetaLogarithmicShiftAllowance
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.ZetaNearOneLogProfile
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have he : (y - x) / x = y / x - 1 := by field_simp
  rw [he]
  linarith

theorem height_shift_le (t a u : ℝ) : height (t + a * u) ≤ height t + |a| * |u| := by
  have h := abs_add_le t (a * u)
  rw [abs_mul] at h
  unfold height
  linarith

def shiftCost (k : ℕ) (t a : ℝ) : ℝ :=
  (alpha k + (Real.log (height t))⁻¹) * |a| / height t

theorem shiftCost_nonneg (k : ℕ) (t a : ℝ) : 0 ≤ shiftCost k t a := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  have ha := alpha_pos k
  unfold shiftCost
  positivity

theorem shiftCost_le (k : ℕ) (t a : ℝ) : shiftCost k t a ≤ 3 * |a| / height t := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : (1 / 2 : ℝ) ≤ Real.log (height t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (two_le_height t)
    linarith [Real.log_two_gt_d9]
  have hi : (Real.log (height t))⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hl
    norm_num only [one_div, inv_div, inv_one, mul_one] at h
    exact h
  unfold shiftCost
  apply div_le_div_of_nonneg_right _ hh.le
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
  linarith [alpha_le_half k]

theorem profile_shift_le (k : ℕ) (t a u : ℝ) :
    profile k (t + a * u) ≤ profile k t + shiftCost k t a * |u| := by
  have ht : 0 < height t := by linarith [two_le_height t]
  have hu : 0 < height (t + a * u) := by linarith [two_le_height (t + a * u)]
  have hlt : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  have hlu : 0 < Real.log (height (t + a * u)) :=
    Real.log_pos (by linarith [two_le_height (t + a * u)])
  let q : ℝ := |a| * |u| / height t
  have hheight : (height (t + a * u) - height t) / height t ≤ q := by
    apply div_le_div_of_nonneg_right _ ht.le
    linarith [height_shift_le t a u]
  have hl : Real.log (height (t + a * u)) ≤ Real.log (height t) + q := by
    linarith [log_le_tangent ht hu]
  have hd : (Real.log (height (t + a * u)) - Real.log (height t)) /
      Real.log (height t) ≤ q / Real.log (height t) := by
    apply div_le_div_of_nonneg_right _ hlt.le
    linarith
  have hll : Real.log (Real.log (height (t + a * u))) ≤
      Real.log (Real.log (height t)) + q / Real.log (height t) := by
    linarith [log_le_tangent hlt hlu]
  have hm := mul_le_mul_of_nonneg_left hl (alpha_pos k).le
  calc
    _ ≤ Real.log (32768 / DerivativeOrderComparison.delta k) +
        alpha k * (Real.log (height t) + q) +
        (Real.log (Real.log (height t)) + q / Real.log (height t)) := by
      unfold profile
      linarith
    _ = _ := by unfold profile shiftCost; dsimp [q]; ring

end
end RiemannGaussian.ZetaLogarithmicShiftAllowance
