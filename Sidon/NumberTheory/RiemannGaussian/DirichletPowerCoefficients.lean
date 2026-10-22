/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
import Sidon.NumberTheory.RiemannGaussian.LogarithmicDerivativeFamily

namespace RiemannGaussian.DirichletPowerCoefficients
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.LogarithmicDerivativeFamily
def factor (k : ℕ) : ℝ := ((k + 1).factorial : ℝ) / (2 : ℝ) ^ (k + 2)

theorem factor_pos (k : ℕ) : 0 < factor k := by
  unfold factor
  positivity

theorem factorial_le_double_power (k : ℕ) : (k + 1).factorial ≤ (2 : ℕ) ^ (2 ^ k) := by
  have hlin : ∀ j : ℕ, j + 1 ≤ (2 : ℕ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; omega
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : k + 2 ≤ (2 : ℕ) ^ (2 ^ k) :=
      (hlin (k + 1)).trans (pow_le_pow_right₀ (by norm_num) (hlin k))
    rw [Nat.factorial_succ]
    calc
      _ ≤ ((2 : ℕ) ^ (2 ^ k)) * ((2 : ℕ) ^ (2 ^ k)) := Nat.mul_le_mul hk ih
      _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

theorem double_power_exponent_le_one (k : ℕ) : (2 : ℝ) ^ k * alpha k ≤ 1 := by
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  rw [pow_add]
  norm_num
  nlinarith

theorem factor_positive_power_le_two (k : ℕ) : factor k ^ alpha k ≤ 2 := by
  have hf : ((k + 1).factorial : ℝ) ≤ (2 : ℝ) ^ (2 ^ k) := by
    exact_mod_cast factorial_le_double_power k
  have hfac : factor k ≤ (2 : ℝ) ^ (2 ^ k) := by
    apply (div_le_self (by positivity : (0 : ℝ) ≤ (k + 1).factorial)
      (one_le_pow₀ (by norm_num))).trans hf
  have he : (((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using double_power_exponent_le_one k
  calc
    _ ≤ ((2 : ℝ) ^ (2 ^ k)) ^ alpha k :=
      Real.rpow_le_rpow (factor_pos k).le hfac (alpha_pos k).le
    _ = (2 : ℝ) ^ ((((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

theorem factor_negative_power_le_two (k : ℕ) : factor k ^ (-alpha k) ≤ 2 := by
  have hf : (1 : ℝ) ≤ (k + 1).factorial := by
    exact_mod_cast (Nat.factorial_pos (k + 1))
  have hi : 1 / factor k ≤ (2 : ℝ) ^ (k + 2) := by
    unfold factor
    rw [one_div_div]
    exact div_le_self (by positivity) hf
  have he : ((k + 2 : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using order_mul_alpha_le_one k
  calc
    _ = (1 / factor k) ^ alpha k := by
      rw [Real.div_rpow (by norm_num) (factor_pos k).le, Real.one_rpow,
        Real.rpow_neg (factor_pos k).le, one_div]
    _ ≤ ((2 : ℝ) ^ (k + 2)) ^ alpha k :=
      Real.rpow_le_rpow (one_div_pos.mpr (factor_pos k)).le hi (alpha_pos k).le
    _ = (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

theorem lowerScale_eq_factor (t X : ℝ) (k : ℕ) :
    lowerScale t X k = factor k * t / X ^ (k + 2) := by
  unfold lowerScale factor
  rw [mul_pow]
  ring

theorem scale_power (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X) (q : ℝ) :
    lowerScale t X k ^ q = factor k ^ q * t ^ q * X ^ (-((k : ℝ) + 2) * q) := by
  rw [lowerScale_eq_factor,
    Real.div_rpow (mul_nonneg (factor_pos k).le ht.le) (by positivity),
    Real.mul_rpow (factor_pos k).le ht.le,
    ← Real.rpow_natCast_mul hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le]
  congr 2
  push_cast
  ring

end
end RiemannGaussian.DirichletPowerCoefficients
