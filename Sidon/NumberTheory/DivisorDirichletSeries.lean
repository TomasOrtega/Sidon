module

public import Sidon.NumberTheory.DivisorMeanSquare
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Convolution

@[expose] public section

/-! # Absolutely convergent divisor Dirichlet series -/

noncomputable section

namespace Sidon

theorem LSeriesHasSum_nat_convolution {f g : ArithmeticFunction ℕ} {s a b : ℂ}
    (hf : LSeriesHasSum (fun n => (f n : ℂ)) s a)
    (hg : LSeriesHasSum (fun n => (g n : ℂ)) s b) :
    LSeriesHasSum (fun n => ((f * g) n : ℂ)) s (a * b) := by
  have hh := ArithmeticFunction.LSeriesHasSum_mul (f := (f : ArithmeticFunction ℂ))
    (g := (g : ArithmeticFunction ℂ)) hf hg
  simpa only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply] using hh

/-- The fourth-order divisor convolution has the literal zeta fourth-power series. -/
theorem LSeriesHasSum_fourDivisor {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (fourDivisor n : ℂ)) s (riemannZeta s ^ 4) := by
  have hz : LSeriesHasSum (fun n => (ArithmeticFunction.zeta n : ℂ)) s (riemannZeta s) :=
    ArithmeticFunction.LSeriesHasSum_zeta hs
  have hσ : ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
  have htwo := LSeriesHasSum_nat_convolution hz hz
  rw [← hσ] at htwo
  have hfour := LSeriesHasSum_nat_convolution htwo htwo
  change LSeriesHasSum
    (fun n => (((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) n : ℂ))
    s (riemannZeta s ^ 4)
  convert hfour using 1
  ring

theorem LSeriesSummable_fourDivisor {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fourDivisor n : ℂ)) s :=
  (LSeriesHasSum_fourDivisor hs).LSeriesSummable

/-- Real positive-axis series, with zero terms handled explicitly. -/
theorem hasSum_fourDivisor_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (fourDivisor n : ℝ) / (n : ℝ) ^ σ)
      (riemannZeta (σ : ℂ) ^ 4).re := by
  have hh := Complex.reCLM.hasSum (LSeriesHasSum_fourDivisor
    (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ))
  change HasSum (fun n : ℕ => (fourDivisor n : ℝ) / (n : ℝ) ^ σ)
    (Complex.reCLM (riemannZeta (σ : ℂ) ^ 4))
  convert hh using 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [fourDivisor, LSeries.term]
  · simp only [LSeries.term, hn, ite_false, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_natCast (fourDivisor n),
      ← Complex.ofReal_div, Complex.reCLM_apply, Complex.ofReal_re]

/-- Divisor-square coefficients are dominated by an absolutely convergent zeta fourth power. -/
theorem summable_divisor_sq_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (hasSum_fourDivisor_div_rpow hσ).summable
  intro n
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  exact_mod_cast divisor_sq_le_fourDivisor n

theorem tsum_divisor_sq_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ σ) ≤
      (riemannZeta (σ : ℂ) ^ 4).re := by
  rw [← (hasSum_fourDivisor_div_rpow hσ).tsum_eq]
  apply Summable.tsum_le_tsum _ (summable_divisor_sq_div_rpow hσ)
    (hasSum_fourDivisor_div_rpow hσ).summable
  intro n
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  exact_mod_cast divisor_sq_le_fourDivisor n

end Sidon
