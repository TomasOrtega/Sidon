module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

/-! # Explicit interfaces for primes in short intervals

The power-saving hypothesis below is an input, not an asserted theorem.
-/

noncomputable section

namespace Sidon

/-- Every real interval `[x - C*x^θ, x]` beyond `X` contains a natural prime. -/
def PrimeIntervalBound (θ C X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∃ p : ℕ, p.Prime ∧ x - C * x ^ θ ≤ p ∧ (p : ℝ) ≤ x

theorem PrimeIntervalBound.mono_exponent {θ θ' C X : ℝ}
    (h : PrimeIntervalBound θ C X) (hC : 0 ≤ C) (hθ : θ ≤ θ') :
    PrimeIntervalBound θ' C (max X 1) := by
  intro x hx
  obtain ⟨p, hp, hlow, hupp⟩ := h x ((le_max_left _ _).trans hx)
  refine ⟨p, hp, ?_, hupp⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hrpow : x ^ θ ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx1 hθ
  have := mul_le_mul_of_nonneg_left hrpow hC
  linarith

/-- The published BHP exponent is stronger than the rate needed by Corollary 1.4. -/
theorem PrimeIntervalBound.two_thirds_of_bhp {C X : ℝ}
    (h : PrimeIntervalBound ((21 : ℝ) / 40) C X) (hC : 0 ≤ C) :
    PrimeIntervalBound ((2 : ℝ) / 3) C (max X 1) :=
  h.mono_exponent hC (by norm_num)

end Sidon
