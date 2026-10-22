import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-! # Rounding estimates for averaging windows -/

namespace Sidon

/-- Rounding down a real number at least one loses at most a factor of two. -/
theorem half_le_natFloor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hfloor' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one x
  by_cases hx2 : x ≤ 2 <;> linarith

/-- A rounded power window has the size and positivity needed in differencing. -/
theorem floor_rpow_window_spec {N : ℕ} (hN : 0 < N) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    1 ≤ ⌊(N : ℝ) ^ θ⌋₊ ∧ ⌊(N : ℝ) ^ θ⌋₊ ≤ N ∧
      (N : ℝ) ^ θ / 2 ≤ (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ∧
      (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ := by
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow₁ : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow hN₁ hθ₀
  have hpowN : (N : ℝ) ^ θ ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN₁ hθ₁
  exact ⟨(Nat.one_le_floor_iff _).mpr hpow₁, Nat.floor_le_of_le hpowN,
    half_le_natFloor hpow₁, Nat.floor_le (le_trans (by norm_num) hpow₁)⟩

/-- A convenient nonnegative-root bound for the quadratic inequality in Appendix A. -/
theorem le_add_sqrt_of_sq_le {x b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ b * x + c) : x ≤ b + Real.sqrt c := by
  by_contra hn
  have hx : b + Real.sqrt c < x := lt_of_not_ge hn
  have hs := Real.sqrt_nonneg c
  have hsq := Real.sq_sqrt hc
  have hp : 0 < (x - Real.sqrt c) * (x - b) :=
    mul_pos (by linarith) (by linarith)
  have hq : 0 ≤ Real.sqrt c * (x - b - Real.sqrt c) :=
    mul_nonneg hs (by linarith)
  nlinarith

end Sidon
