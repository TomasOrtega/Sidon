/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents

namespace RiemannGaussian.DirichletPowerParameters
noncomputable section
open RiemannGaussian.DerivativePowerExponents
def line (k : ℕ) : ℝ := 1 - ((k : ℝ) + 2) * alpha k

def slope (k : ℕ) : ℝ := 2 * ((k : ℝ) + 2) * alpha k - amp k

def transition (k : ℕ) : ℝ := 1 / ((k : ℝ) + amp k)

theorem denominator_ge_order (k : ℕ) : (k : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem order_mul_alpha_le_one (k : ℕ) : ((k : ℝ) + 2) * alpha k ≤ 1 := by
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  exact denominator_ge_order k

theorem line_nonneg (k : ℕ) : 0 ≤ line k := by
  unfold line
  linarith [order_mul_alpha_le_one k]

theorem line_lt_one (k : ℕ) : line k < 1 := by
  unfold line
  have hp : 0 < ((k : ℝ) + 2) * alpha k := mul_pos (by positivity) (alpha_pos k)
  linarith

theorem half_le_line_succ (k : ℕ) : 1 / 2 ≤ line (k + 1) := by
  have hb : ∀ j : ℕ, 2 * ((j : ℝ) + 3) + 2 ≤ (2 : ℝ) ^ (j + 3) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hd := denominator_ge_two (k + 1)
  have h : ((k : ℝ) + 3) * alpha (k + 1) ≤ 1 / 2 := by
    unfold alpha
    rw [mul_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    have h := hb k
    rw [show k + 1 + 2 = k + 3 by omega]
    linarith
  unfold line
  push_cast
  linarith

theorem amp_alpha_identity (k : ℕ) : amp k * (1 + 2 * alpha k) = 4 * alpha k := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hd := denominator_ge_two k
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hD : -2 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  unfold amp alpha
  rw [pow_add]
  norm_num
  field_simp
  ring_nf
  field_simp
  ring

theorem slope_eq (k : ℕ) : slope k = 2 * alpha k * ((k : ℝ) + amp k) := by
  unfold slope
  nlinarith [amp_alpha_identity k]

theorem slope_pos (k : ℕ) : 0 < slope k := by
  rw [slope_eq]
  have hp := amp_pos k
  have ha := alpha_pos k
  positivity

theorem transition_balance (k : ℕ) : transition k * slope k = 2 * alpha k := by
  rw [transition, slope_eq]
  have hp : (k : ℝ) + amp k ≠ 0 := ne_of_gt (by have h := amp_pos k; positivity)
  field_simp

end
end RiemannGaussian.DirichletPowerParameters
