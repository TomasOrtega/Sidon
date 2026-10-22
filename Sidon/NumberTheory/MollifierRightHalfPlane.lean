import Sidon.NumberTheory.MollifierSymmetry

/-! # The same boundary bound throughout the right half-plane -/

noncomputable section

open MeasureTheory

namespace Sidon

theorem integral_mollifierError_right_halfPlane_le {N : ℕ} (hN : 1 ≤ N)
    {δ σ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 1 + δ ≤ σ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 := by
  let a (n : ℕ) := LSeries.term (balancedMollifierCoefficient N) (σ : ℂ) n
  let d (n : ℕ) : ℝ := (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)
  let w (n : ℕ) : ℝ :=
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)
  have hcmp (n : ℕ) : ‖a n‖ ≤ ‖rightMollifierCoefficient N δ n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by simpa using hσ) n
  have ha_le (n : ℕ) : ‖a n‖ ≤ d n :=
    (hcmp n).trans (norm_rightMollifierCoefficient_le_sq hN δ n)
  have ha2_le (n : ℕ) : ‖a n‖ ^ 2 ≤ (1 / (N : ℝ)) * d n :=
    (pow_le_pow_left₀ (norm_nonneg _) (hcmp n) 2).trans
      (norm_rightMollifierCoefficient_sq_le hN hδ n)
  have hlog (n : ℕ) : 0 ≤ 1 + Real.log n := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [Real.log_nonneg hn1]
  have haw_le (n : ℕ) : (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) ≤ w n := by
    apply (show (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) ≤
        (n : ℝ) * ‖rightMollifierCoefficient N δ n‖ ^ 2 * (1 + Real.log n) from ?_).trans
      (weighted_norm_rightMollifierCoefficient_sq_le hN δ n)
    gcongr
    exact hcmp n
  have hd : Summable d := summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)
  have hw : Summable w := summable_divisor_sq_log_div_rpow hδ hδ1
  have ha := Summable.of_nonneg_of_le (fun n => norm_nonneg (a n)) ha_le hd
  have ha2 := Summable.of_nonneg_of_le (fun n => sq_nonneg ‖a n‖) ha2_le (hd.mul_left _)
  have haw := Summable.of_nonneg_of_le
    (fun n : ℕ => mul_nonneg (show 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 by positivity) (hlog n)) haw_le hw
  have ha_bound : (∑' n : ℕ, ‖a n‖) ≤ 16 / δ ^ 4 :=
    (Summable.tsum_le_tsum ha_le ha hd).trans (tsum_divisor_sq_div_rpow_le_pole hδ hδ1)
  have ha2_bound : (∑' n : ℕ, ‖a n‖ ^ 2) ≤ 16 / ((N : ℝ) * δ ^ 4) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (N : ℝ)) * d n :=
        Summable.tsum_le_tsum ha2_le ha2 (hd.mul_left _)
      _ = (1 / (N : ℝ)) * ∑' n : ℕ, d n := tsum_mul_left
      _ ≤ (1 / (N : ℝ)) * (16 / δ ^ 4) :=
        mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
      _ = _ := by ring
  have haw_bound : (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) ≤ 32 / δ ^ 5 :=
    (Summable.tsum_le_tsum haw_le haw hw).trans (tsum_divisor_sq_log_div_rpow_le hδ hδ1)
  have heq (t : ℝ) : logarithmicSeries a t = mollifierError N ((σ : ℂ) + t * Complex.I) := by
    have hh := LSeriesHasSum_balancedMollifierCoefficient
      (s := (σ : ℂ) + t * Complex.I) (by simp; linarith) N
    rw [← hh.tsum_eq]
    apply tsum_congr
    intro n
    exact (LSeries_term_vertical _ _ _ _).symm
  have hh := integral_logarithmicSeries_norm_sq_le a (by simp [a]) ha ha2 haw hT
  simp_rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 4 * (16 / δ ^ 4) ^ 2 + 16 * (32 / δ ^ 5) := by
      gcongr
    _ = _ := by ring

end Sidon
