/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DerivativeRecursionBudget

namespace RiemannGaussian.AnalyticDerivativeCutoff
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DerivativeRecursionBudget
def ideal (k : ℕ) (ℓ : ℝ) : ℝ := ℓ ^ (-2 * alpha (k + 1))

def cutoffs : Cutoffs := fun k _ ℓ _ ↦ ⌈ideal k ℓ⌉₊ - 1

theorem ideal_pos (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < ideal k ℓ :=
  Real.rpow_pos_of_pos hℓ _

theorem count_eq (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    shiftCount cutoffs k L ℓ A = ⌈ideal k ℓ⌉₊ := by
  unfold shiftCount cutoffs
  exact Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr (ideal_pos k hℓ))

theorem one_le_ideal (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    1 ≤ ideal k ℓ :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hℓ hℓ1 (by nlinarith [alpha_pos (k + 1)])

theorem ideal_le_count (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    ideal k ℓ ≤ (shiftCount cutoffs k L ℓ A : ℝ) := by
  rw [count_eq k L hℓ A]
  exact Nat.le_ceil _

theorem count_le_twice (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (A : ℝ) :
    (shiftCount cutoffs k L ℓ A : ℝ) ≤ 2 * ideal k ℓ := by
  rw [count_eq k L hℓ A]
  have h := Nat.ceil_lt_add_one (ideal_pos k hℓ).le
  linarith [one_le_ideal k hℓ hℓ1]

theorem length_lt_ideal (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ)
    (hL : L < shiftCount cutoffs k L ℓ A) : (L : ℝ) < ideal k ℓ := by
  rw [count_eq k L hℓ A] at hL
  exact Nat.lt_ceil.mp hL

theorem ideal_mul (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ideal k ℓ * ℓ = ℓ ^ (1 - 2 * alpha (k + 1)) := by
  rw [show 1 - 2 * alpha (k + 1) = -2 * alpha (k + 1) + 1 by ring,
    Real.rpow_add hℓ, Real.rpow_one]
  rfl

theorem ideal_positive_power (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (ideal k ℓ * ℓ) ^ alpha k = ℓ ^ (2 * alpha (k + 1)) := by
  rw [ideal_mul k hℓ, ← Real.rpow_mul hℓ.le]
  rw [mul_comm, alpha_balance]

theorem ideal_negative_power (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (ideal k ℓ * ℓ) ^ (-alpha k) = ideal k ℓ := by
  rw [Real.rpow_neg (mul_nonneg (ideal_pos k hℓ).le hℓ.le), ideal_positive_power k hℓ,
    ← Real.rpow_neg hℓ.le]
  unfold ideal
  congr 1
  ring

theorem count_positive_power (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (A : ℝ) :
    ((shiftCount cutoffs k L ℓ A : ℝ) * ℓ) ^ alpha k ≤
      2 * ℓ ^ (2 * alpha (k + 1)) := by
  have hc := count_le_twice k L hℓ hℓ1 A
  have htwo : (2 : ℝ) ^ alpha k ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show alpha k ≤ 1 by linarith [alpha_le_half k])
  calc
    _ ≤ (2 * (ideal k ℓ * ℓ)) ^ alpha k := by
      apply Real.rpow_le_rpow (by positivity) _ (alpha_pos k).le
      nlinarith [mul_le_mul_of_nonneg_right hc hℓ.le]
    _ = (2 : ℝ) ^ alpha k * ℓ ^ (2 * alpha (k + 1)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg (ideal_pos k hℓ).le hℓ.le), ideal_positive_power k hℓ]
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)

theorem count_negative_power (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    ((shiftCount cutoffs k L ℓ A : ℝ) * ℓ) ^ (-alpha k) ≤ ideal k ℓ := by
  rw [← ideal_negative_power k hℓ]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (ideal_pos k hℓ) hℓ)
    (mul_le_mul_of_nonneg_right (ideal_le_count k L hℓ A) hℓ.le)
    (by linarith [alpha_pos k])

theorem inv_count_le (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    1 / (shiftCount cutoffs k L ℓ A : ℝ) ≤ ℓ ^ (2 * alpha (k + 1)) := by
  calc
    _ ≤ 1 / ideal k ℓ := one_div_le_one_div_of_le (ideal_pos k hℓ) (ideal_le_count k L hℓ A)
    _ = _ := by
      unfold ideal
      rw [show -2 * alpha (k + 1) = -(2 * alpha (k + 1)) by ring,
        Real.rpow_neg hℓ.le, one_div, inv_inv]

end
end RiemannGaussian.AnalyticDerivativeCutoff
