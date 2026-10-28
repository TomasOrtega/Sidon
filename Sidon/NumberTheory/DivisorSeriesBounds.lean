module

public import Sidon.NumberTheory.DivisorDirichletSeries
public import Sidon.NumberTheory.PSeriesBounds

@[expose] public section

/-! # Uniform pole bounds for divisor-square coefficient sums -/

noncomputable section

namespace Sidon

theorem tsum_divisor_sq_div_rpow_le_pole {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) ≤ 16 / δ ^ 4 := by
  have hs : 1 < 1 + δ := by linarith
  have hz := norm_riemannZeta_le_pole (s := ((1 + δ : ℝ) : ℂ))
    (by simpa only [Complex.ofReal_re] using hs)
  simp only [Complex.ofReal_re, add_sub_cancel_left] at hz
  have hbound : 1 + 1 / δ ≤ 2 / δ := by
    apply (le_div_iff₀ hδ).mpr
    field_simp
    linarith
  calc
    _ ≤ (riemannZeta ((1 + δ : ℝ) : ℂ) ^ 4).re := tsum_divisor_sq_div_rpow_le hs
    _ ≤ ‖riemannZeta ((1 + δ : ℝ) : ℂ) ^ 4‖ := Complex.re_le_norm _
    _ = ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖ ^ 4 := norm_pow _ _
    _ ≤ (2 / δ) ^ 4 := by gcongr; exact hz.trans hbound
    _ = _ := by ring

/-- A logarithmic weight costs one additional pole order. -/
theorem divisor_sq_log_term_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ) ≤
      (2 / δ) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
    have hlog := Real.log_le_rpow_div hn0.le hδ
    have hlogbound : 1 + Real.log n ≤ (2 / δ) * (n : ℝ) ^ δ := by
      have hfirst : 1 ≤ (n : ℝ) ^ δ / δ :=
        (le_div_iff₀ hδ).mpr (by nlinarith)
      have hh : 1 + Real.log n ≤ 2 * ((n : ℝ) ^ δ / δ) := by linarith
      convert hh using 1 <;> ring
    have heq : (n : ℝ) ^ (1 + 2 * δ) = (n : ℝ) ^ (1 + δ) * (n : ℝ) ^ δ := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ (n.divisors.card : ℝ) ^ 2 * ((2 / δ) * (n : ℝ) ^ δ) /
          ((n : ℝ) ^ (1 + δ) * (n : ℝ) ^ δ) := by gcongr
      _ = _ := by field_simp

theorem summable_divisor_sq_log_div_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable (fun n : ℕ =>
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)) := by
  apply Summable.of_nonneg_of_le _ (divisor_sq_log_term_le hδ hδ1)
    ((summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)).mul_left (2 / δ))
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hn1]))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem tsum_divisor_sq_log_div_rpow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) /
      (n : ℝ) ^ (1 + 2 * δ)) ≤ 32 / δ ^ 5 := by
  calc
    _ ≤ ∑' n : ℕ, (2 / δ) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) :=
      Summable.tsum_le_tsum (divisor_sq_log_term_le hδ hδ1)
        (summable_divisor_sq_log_div_rpow hδ hδ1)
        ((summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)).mul_left (2 / δ))
    _ = (2 / δ) * ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ) := tsum_mul_left
    _ ≤ (2 / δ) * (16 / δ ^ 4) :=
      mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
    _ = _ := by ring

end Sidon
