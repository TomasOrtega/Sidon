module

public import Sidon.NumberTheory.BSplineKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Closed forms for the integrated step function used by the prime detector. -/

noncomputable section

open MeasureTheory

namespace Sidon

theorem heavisidePrimitive_succ_eq_pow (n : ℕ) (u : ℝ) :
    heavisidePrimitive (n + 1) u = (max u 0) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  induction n generalizing u with
  | zero => simp [heavisidePrimitive_one]
  | succ n ih =>
      by_cases hu : 0 ≤ u
      · change (∫ v in (0 : ℝ)..u, heavisidePrimitive (n + 1) v) = _
        calc
          _ = ∫ v in (0 : ℝ)..u, v ^ (n + 1) / ((n + 1).factorial : ℝ) := by
            apply intervalIntegral.integral_congr
            intro v hv
            rw [Set.uIcc_of_le hu] at hv
            rw [ih, max_eq_left hv.1]
          _ = u ^ (n + 1 + 1) / (n + 1 + 1 : ℕ) / ((n + 1).factorial : ℝ) := by
            rw [intervalIntegral.integral_div, integral_pow]
            simp only [zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero]
            norm_num
          _ = (max u 0) ^ (n + 1 + 1) / (((n + 1 + 1).factorial : ℕ) : ℝ) := by
            rw [max_eq_left hu, Nat.factorial_succ (n + 1), Nat.cast_mul, div_div]
      · have hu' : u ≤ 0 := (lt_of_not_ge hu).le
        rw [heavisidePrimitive_succ_eq_zero_of_nonpos (n + 1) hu', max_eq_right hu']
        simp

end Sidon
