/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovDiagonalExponent
import Sidon.NumberTheory.RiemannGaussian.VinogradovDiagonalIteration
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovNarrowThreshold
import Sidon.NumberTheory.RiemannGaussian.VinogradovPowerSumRigidity

namespace RiemannGaussian.VinogradovNarrowIteration
noncomputable section
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovDiagonalExponent
open RiemannGaussian.VinogradovDiagonalIteration RiemannGaussian.VinogradovNarrowThreshold
def coefficient (k : ℕ) : ℕ → ℕ
  | 0 => k.factorial
  | n + 1 => nextCoefficient k (order k n) (coefficient k n)

theorem iterated_moment_bound {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∀ P : ℕ, 1 ≤ P → meanValue (order k n) k P ≤
      (coefficient k n : ℝ) * (P : ℝ) ^ exponent k (order k n) (defect k n) := by
  induction n with
  | zero =>
    intro P hP
    have h := VinogradovPowerSumRigidity.meanValue_le (r := k) (k := k) (N := P) le_rfl
    rw [initial_exponent, Real.rpow_natCast]
    simpa only [order, zero_add, one_mul, coefficient, mul_comm, Nat.mul_one] using h
  | succ n ih =>
    intro P hP
    have hs : 1 ≤ order k n := by
      unfold order
      exact Nat.mul_pos (by omega) (by omega)
    have h := all_endpoint_defect_step hk hs (defect_nonneg (by omega) n)
      (defect_le_square (by omega) n) (exponent_nonneg (by omega) n) ih P hP
    simpa only [coefficient, order_succ, defect_succ] using h

theorem relative_moment_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((7 * k + 1) * k) k P ≤ (coefficient k (7 * k) : ℝ) *
      (P : ℝ) ^ (2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256) := by
  have h := iterated_moment_bound hk (7 * k) P hP
  have he : exponent k (order k (7 * k)) (defect k (7 * k)) ≤
      2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256 := by
    unfold exponent order
    rw [degreeWeight_cast (by omega)]
    linarith [defect_seven_degree_le (by omega : 1 ≤ k)]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP) he) (Nat.cast_nonneg _))

end
end RiemannGaussian.VinogradovNarrowIteration
