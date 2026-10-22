/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace RiemannGaussian.DerivativePowerExponents
noncomputable section

def alpha (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (k + 2) - 2)

def amp (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

def beta (k : ℕ) : ℝ := 1 - amp k

theorem denominator_ge_two (k : ℕ) : 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  have h : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  linarith

theorem alpha_pos (k : ℕ) : 0 < alpha k := by
  unfold alpha
  have h := denominator_ge_two k
  positivity

theorem alpha_le_half (k : ℕ) : alpha k ≤ 1 / 2 := by
  have h := denominator_ge_two k
  unfold alpha
  apply (div_le_iff₀ (by linarith : 0 < (2 : ℝ) ^ (k + 2) - 2)).mpr
  linarith

theorem alpha_zero : alpha 0 = 1 / 2 := by norm_num [alpha]

theorem alpha_succ (k : ℕ) : alpha (k + 1) = alpha k / (2 + 2 * alpha k) := by
  have h := denominator_ge_two k
  unfold alpha
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hB : -1 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  field_simp
  ring_nf
  field_simp

theorem alpha_balance (k : ℕ) : alpha k * (1 - 2 * alpha (k + 1)) = 2 * alpha (k + 1) := by
  rw [alpha_succ]
  have h := alpha_pos k
  field_simp
  ring

theorem amp_pos (k : ℕ) : 0 < amp k := by
  unfold amp
  positivity

theorem amp_le_one (k : ℕ) : amp k ≤ 1 := by
  unfold amp
  exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr (one_le_pow₀ (by norm_num))

theorem amp_zero : amp 0 = 1 := by norm_num [amp]

theorem amp_succ (k : ℕ) : amp (k + 1) = amp k / 2 := by
  unfold amp
  rw [pow_succ]
  ring

theorem beta_nonneg (k : ℕ) : 0 ≤ beta k := sub_nonneg.mpr (amp_le_one k)

theorem beta_zero : beta 0 = 0 := by norm_num [beta, amp]

theorem beta_succ (k : ℕ) : beta (k + 1) = (beta k + 1) / 2 := by
  unfold beta
  rw [amp_succ]
  ring

end
end RiemannGaussian.DerivativePowerExponents
