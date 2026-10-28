module

public import Sidon.Analysis.TorusFourier

@[expose] public section

/-! # Finitely supported trigonometric polynomials on the torus -/

noncomputable section

open scoped BigOperators

namespace Sidon

def torusPolynomial {d : ℕ} (a : (Fin d → ℤ) →₀ ℂ) :
    C(Fin d → AddCircle (1 : ℝ), ℂ) :=
  a.sum fun n c => c • torusCharacter n

@[simp] theorem torusPolynomial_apply {d : ℕ} (a : (Fin d → ℤ) →₀ ℂ)
    (x : Fin d → AddCircle (1 : ℝ)) :
    torusPolynomial a x = ∑ n ∈ a.support, a n * torusCharacter n x := by
  simp only [torusPolynomial, Finsupp.sum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]

def HasTorusBandwidth {d : ℕ} (a : (Fin d → ℤ) →₀ ℂ) (M : ℕ) : Prop :=
  ∀ n ∈ a.support, ∀ i, |n i| ≤ (M : ℤ)

end Sidon
