module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic

@[expose] public section

/-! # Finite normalized Dirichlet-convolution bounds -/

noncomputable section

namespace Sidon

/-- The natural denominator is interpreted in `ℝ`, including its zero convention. -/
def normalizeArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / n, by simp⟩

@[simp] theorem normalizeArithmetic_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    normalizeArithmetic f n = f n / n := rfl

theorem normalizeArithmetic_mul (f g : ArithmeticFunction ℝ) :
    normalizeArithmetic (f * g) = normalizeArithmetic f * normalizeArithmetic g := by
  ext n
  rw [normalizeArithmetic_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have hmul := (Nat.mem_divisorsAntidiagonal.mp ha).1
  simp only [normalizeArithmetic_apply]
  rw [← hmul, Nat.cast_mul]
  ring

/-- Dropping the product cutoff bounds the summatory convolution by a product. -/
theorem sum_Ioc_convolution_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Ioc 0 N, (f * g) n) ≤
      (∑ n ∈ Finset.Ioc 0 N, f n) * ∑ n ∈ Finset.Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, Finset.sum_mul_sum]
  have hh : (∑ a ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun a => a.1 * a.2 ≤ N),
      f a.1 * g a.2) ≤ ∑ a ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N, f a.1 * g a.2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a _ _
    exact mul_nonneg (hf _) (hg _)
  simpa only [Finset.sum_product] using hh

/-- A weighted convolution bound, uniform in the finite endpoint. -/
theorem sum_Ioc_convolution_div_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Ioc 0 N, (f * g) n / n) ≤
      (∑ n ∈ Finset.Ioc 0 N, f n / n) * ∑ n ∈ Finset.Ioc 0 N, g n / n := by
  simpa only [← normalizeArithmetic_mul, normalizeArithmetic_apply] using
    sum_Ioc_convolution_le (normalizeArithmetic f) (normalizeArithmetic g) N
      (fun n => div_nonneg (hf n) (Nat.cast_nonneg n))
      (fun n => div_nonneg (hg n) (Nat.cast_nonneg n))

end Sidon
