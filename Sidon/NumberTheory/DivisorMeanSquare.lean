import Sidon.NumberTheory.ArithmeticConvolutionBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # Divisor second moments and fourth-order divisor convolution -/

noncomputable section

namespace Sidon

open scoped ArithmeticFunction.sigma

/-- Four ordered positive factors, expressed as a Dirichlet convolution. -/
def fourDivisor : ArithmeticFunction ℕ := (ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)

theorem divisor_sq_le_fourDivisor_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (ArithmeticFunction.sigma 0 (p ^ e)) ^ 2 ≤ fourDivisor (p ^ e) := by
  rw [fourDivisor, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.sigma 0 a * ArithmeticFunction.sigma 0 b),
    Nat.sum_divisors_prime_pow hp, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  calc
    (e + 1) ^ 2 = ∑ _k ∈ Finset.range (e + 1), (e + 1) := by simp [pow_two]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hke : k ≤ e := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      have hdiv : p ^ e / p ^ k = p ^ (e - k) := Nat.pow_div hke hp.pos
      rw [hdiv, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have heq : e = k + (e - k) := by omega
      nlinarith [Nat.zero_le (k * (e - k))]

/-- The pointwise square of the divisor function is bounded by its Dirichlet square. -/
theorem divisor_sq_le_fourDivisor (n : ℕ) :
    n.divisors.card ^ 2 ≤ fourDivisor n := by
  by_cases hn : n = 0
  · subst n
    simp [fourDivisor]
  · have hσ := ArithmeticFunction.isMultiplicative_sigma (k := 0)
    have hleft := hσ.pmul hσ
    have hright := hσ.mul hσ
    rw [← ArithmeticFunction.sigma_zero_apply, pow_two]
    change ((ArithmeticFunction.sigma 0).pmul (ArithmeticFunction.sigma 0)) n ≤
      ((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) n
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hleft hn,
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hright hn]
    unfold Finsupp.prod
    apply Finset.prod_le_prod
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    simpa only [ArithmeticFunction.pmul_apply, pow_two, fourDivisor] using
      divisor_sq_le_fourDivisor_prime_pow hpprime (n.factorization p)

theorem sum_Ioc_nat_convolution_div_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℝ) / n) ≤
      (∑ n ∈ Finset.Ioc 0 N, (f n : ℝ) / n) *
        ∑ n ∈ Finset.Ioc 0 N, (g n : ℝ) / n := by
  simpa only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply] using
    sum_Ioc_convolution_div_le (f : ArithmeticFunction ℝ) (g : ArithmeticFunction ℝ) N
      (fun n => Nat.cast_nonneg (f n)) (fun n => Nat.cast_nonneg (g n))

theorem sum_Ioc_zeta_div (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.zeta n : ℝ) / n) = (harmonic N : ℝ) := by
  have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  rw [hI, harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [ArithmeticFunction.zeta_apply_ne hn0, Nat.cast_one, one_div]

/-- A reciprocal divisor sum is bounded by two harmonic factors. -/
theorem sum_Ioc_divisor_div_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n) ≤ (harmonic N : ℝ) ^ 2 := by
  have hσ : ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
  have hh := sum_Ioc_nat_convolution_div_le ArithmeticFunction.zeta ArithmeticFunction.zeta N
  rw [← hσ] at hh
  simpa only [ArithmeticFunction.sigma_zero_apply, sum_Ioc_zeta_div, pow_two] using hh

/-- The mild fourth logarithmic loss suffices for Ingham's zero-density exponent. -/
theorem sum_Ioc_fourDivisor_div_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) / n) ≤ (harmonic N : ℝ) ^ 4 := by
  have hh := sum_Ioc_nat_convolution_div_le (ArithmeticFunction.sigma 0)
    (ArithmeticFunction.sigma 0) N
  have hσ := sum_Ioc_divisor_div_le N
  simp only [ArithmeticFunction.sigma_zero_apply] at hh
  calc
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n) *
        ∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n := hh
    _ ≤ (harmonic N : ℝ) ^ 2 * (harmonic N : ℝ) ^ 2 :=
      mul_le_mul hσ hσ (by positivity) (sq_nonneg _)
    _ = _ := by ring

/-- A uniform finite divisor-square bound, without an asymptotic hypothesis. -/
theorem sum_Ioc_divisor_sq_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 4 := by
  have hpoint : (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) := by
    apply Finset.sum_le_sum
    intro n _
    exact_mod_cast divisor_sq_le_fourDivisor n
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) := hpoint
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) / n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hn0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hnN (Nat.cast_nonneg (fourDivisor n) :
        (0 : ℝ) ≤ fourDivisor n)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ioc_fourDivisor_div_le N) (Nat.cast_nonneg N)

end Sidon
