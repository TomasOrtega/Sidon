/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
import Sidon.NumberTheory.RiemannGaussian.ZetaEulerCell
import Sidon.NumberTheory.RiemannGaussian.ZetaEulerLineBound
import Sidon.NumberTheory.RiemannGaussian.ZetaEulerTruncation
import Sidon.NumberTheory.RiemannGaussian.ZetaEulerUniformRemainder
import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer
import Sidon.NumberTheory.RiemannGaussian.ZetaLogarithmicShiftAllowance
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

namespace RiemannGaussian.ZetaEulerLogProfile
noncomputable section
open Complex RiemannGaussian.ZetaEulerCell RiemannGaussian.ZetaEulerTruncation RiemannGaussian.ZetaGaussianLocalizer
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.ZetaNearOneLogProfile RiemannGaussian.ZetaLogarithmicShiftAllowance
theorem regularized_eq_euler {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) (N : ℕ) :
    regularized s = (s - 1) / (s + 1) * (partialSum N s + remainder N s) +
      (N + 1 : ℂ) ^ (1 - s) / (s + 1) := by
  rw [regularized_eq hsne, zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N]
  field_simp [sub_ne_zero.mpr hsne, add_one_ne_zero hs.le]
  ring

theorem low_height_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (ht : |s.im| ≤ 2) : ‖regularized s‖ ≤ 4 := by
  by_cases hsne : s = 1
  · subst s
    norm_num [regularized, riemannZeta₁_one, norm_div]
  have h := ZetaEulerUniformRemainder.norm_remainder_le_power hs hs1 1 (by norm_num; exact ht)
  norm_num only [Nat.cast_one, one_add_one_eq_two] at h
  have hp : (2 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hr : ‖remainder 1 s‖ ≤ 1 := h.trans hp
  have hpref : partialSum 1 s = 1 := by simp [partialSum]
  have hsum : ‖partialSum 1 s + remainder 1 s‖ ≤ 2 := by
    rw [hpref]
    have h := norm_add_le (1 : ℂ) (remainder 1 s)
    norm_num at h
    linarith
  have hden : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [add_re, one_re] at h
    linarith
  have he : ‖(2 : ℂ) ^ (1 - s) / (s + 1)‖ ≤ 2 := by
    rw [norm_div]
    have hn : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
      simpa only [ofReal_ofNat, sub_re, one_re] using
        norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - s)
    rw [hn]
    apply (div_le_self (by positivity) hden).trans
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - s.re ≤ 1)).trans_eq (Real.rpow_one _)
  rw [regularized_eq_euler hs hsne 1]
  norm_num only [Nat.cast_one, one_add_one_eq_two]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hm := mul_le_mul (norm_ratio_le_one hs.le) hsum (norm_nonneg _) (by norm_num)
  linarith

def profile (k : ℕ) (t : ℝ) : ℝ :=
  Real.log 8192 + alpha k * Real.log (height t) + Real.log (Real.log (height t))

def gain (k : ℕ) : ℝ := Real.log (4 / delta k)

theorem profile_add_gain (k : ℕ) (t : ℝ) :
    profile k t + gain k = ZetaNearOneLogProfile.profile k t := by
  have hc : Real.log (32768 / delta k) = Real.log 8192 + gain k := by
    unfold gain
    rw [← Real.log_mul (by norm_num : (8192 : ℝ) ≠ 0)
      (div_pos (by norm_num) (delta_pos k)).ne']
    congr 1
    ring
  unfold profile ZetaNearOneLogProfile.profile
  rw [hc]
  ring

theorem profile_eq_log (k : ℕ) (t : ℝ) :
    profile k t = Real.log (8192 * height t ^ alpha k * Real.log (height t)) := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 8192)
    (Real.rpow_pos_of_pos hh _)).ne' hl.ne',
    Real.log_mul (by norm_num : (8192 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hh _).ne', Real.log_rpow hh]
  rfl

theorem majorant_lower (k : ℕ) (t : ℝ) :
    (4096 : ℝ) ≤ 8192 * height t ^ alpha k * Real.log (height t) := by
  have hp : 1 ≤ height t ^ alpha k :=
    Real.one_le_rpow (by linarith [two_le_height t]) (alpha_pos k).le
  have hl : (1 / 2 : ℝ) ≤ Real.log (height t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (two_le_height t)
    linarith [Real.log_two_gt_d9]
  nlinarith

theorem profile_ge_six (k : ℕ) (t : ℝ) : 6 ≤ profile k t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4096) (majorant_lower k t)
  rw [← profile_eq_log] at h
  have he : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

theorem regularized_le_exp_profile (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) : ‖regularized s‖ ≤ Real.exp (profile k s.im) := by
  rw [profile_eq_log, Real.exp_log (by linarith [majorant_lower k s.im])]
  have hs : 0 < s.re := by rw [hline]; linarith [half_le_line k hk]
  have hs1 : s.re < 1 := by rw [hline]; exact line_lt_one k
  by_cases ht : 2 ≤ |s.im|
  · have hsne : s ≠ 1 := by intro h; simp [h] at hs1
    have h := (norm_regularized_le_zeta hs.le hsne).trans
      (ZetaEulerLineBound.bound_abs k hk hline ht)
    have hp := Real.rpow_le_rpow (abs_nonneg s.im)
      (show |s.im| ≤ height s.im by unfold height; linarith) (alpha_pos k).le
    have hl := Real.log_le_log (by linarith : 0 < |s.im|)
      (show |s.im| ≤ height s.im by unfold height; linarith)
    have hm := mul_le_mul hp hl (Real.log_nonneg (by linarith))
      (Real.rpow_nonneg (by linarith [two_le_height s.im]) _)
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 8192)
    simpa only [mul_assoc] using h'
  · exact (low_height_bound hs hs1.le (lt_of_not_ge ht).le).trans
      ((by norm_num : (4 : ℝ) ≤ 4096).trans (majorant_lower k s.im))

theorem profile_shift_le (k : ℕ) (t a u : ℝ) :
    profile k (t + a * u) ≤ profile k t + shiftCost k t a * |u| := by
  have h := ZetaLogarithmicShiftAllowance.profile_shift_le k t a u
  rw [← profile_add_gain k (t + a * u), ← profile_add_gain k t] at h
  linarith

end
end RiemannGaussian.ZetaEulerLogProfile
