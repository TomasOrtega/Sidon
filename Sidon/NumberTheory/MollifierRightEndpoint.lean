module

public import Sidon.NumberTheory.InfiniteDirichletMeanSquare
public import Sidon.NumberTheory.BalancedMollifierSeries
public import Sidon.NumberTheory.DivisorSeriesBounds
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

/-! # The absolutely convergent boundary mean square of the balanced mollifier -/

noncomputable section

namespace Sidon

def rightMollifierCoefficient (N : ℕ) (δ : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (balancedMollifierCoefficient N) ((1 + δ : ℝ) : ℂ) n

theorem norm_rightMollifierCoefficient_le {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ≤
      (n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ) := by
  rw [rightMollifierCoefficient, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right (norm_balancedMollifierCoefficient_le hN n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_rightMollifierCoefficient_le_sq {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ≤
      (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ) := by
  apply (norm_rightMollifierCoefficient_le hN δ n).trans
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  simpa only [pow_two] using
    (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
      exact_mod_cast Nat.le_mul_self n.divisors.card)

theorem norm_rightMollifierCoefficient_sq_le {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ^ 2 ≤
      (1 / (N : ℝ)) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) := by
  by_cases hnN : n ≤ N
  · have hz := balancedMollifierCoefficient_eq_zero hnN
    have hzero : rightMollifierCoefficient N δ n = 0 := by
      simp [rightMollifierCoefficient, LSeries.term, hz]
    rw [hzero, norm_zero]
    norm_num only [zero_pow, OfNat.ofNat_ne_zero]
    positivity
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow0 : 0 < (n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn0 _
    have hpowN : (N : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
      have hh : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
      exact hh.trans (Real.self_le_rpow_of_one_le hn1 (by linarith))
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_rightMollifierCoefficient_le hN δ n) 2
    rw [div_pow] at hh
    apply hh.trans
    rw [one_div, div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos hpow0)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hpowN (sq_nonneg (n.divisors.card : ℝ))]

theorem weighted_norm_rightMollifierCoefficient_sq_le {N : ℕ} (hN : 1 ≤ N)
    (δ : ℝ) (n : ℕ) :
    (n : ℝ) * ‖rightMollifierCoefficient N δ n‖ ^ 2 * (1 + Real.log n) ≤
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ 1 + Real.log n := by linarith [Real.log_nonneg hn1]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_rightMollifierCoefficient_le hN δ n) 2
    calc
      _ ≤ (n : ℝ) * ((n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ)) ^ 2 *
          (1 + Real.log n) := by gcongr
      _ = _ := by
        have heq : ((n : ℝ) ^ (1 + δ)) ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 + 2 * δ) := by
          calc
            _ = (n : ℝ) ^ ((1 + δ) * 2) := by rw [Real.rpow_mul hn0.le, Real.rpow_two]
            _ = (n : ℝ) ^ (1 + (1 + 2 * δ)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one]
        rw [div_pow, heq]
        field_simp

theorem LSeries_term_vertical (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f ((σ : ℂ) + t * Complex.I) n =
      LSeries.term f (σ : ℂ) n * frequencyChar (-Real.log n) t := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    unfold frequencyChar
    simp_rw [Complex.cpow_def_of_ne_zero hnC,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    rw [div_mul_eq_div_mul_one_div, one_div, ← Complex.exp_neg]
    congr 2
    push_cast
    ring

theorem logarithmicSeries_rightMollifierCoefficient {N : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (t : ℝ) :
    logarithmicSeries (rightMollifierCoefficient N δ) t =
      mollifierError N ((1 + δ : ℝ) + t * Complex.I) := by
  have hh := LSeriesHasSum_balancedMollifierCoefficient
    (s := ((1 + δ : ℝ) : ℂ) + t * Complex.I) (by simp; linarith) N
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro n
  exact (LSeries_term_vertical _ _ _ _).symm

theorem integral_mollifierError_right_norm_sq_le {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 := by
  let a := rightMollifierCoefficient N δ
  let d (n : ℕ) : ℝ := (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)
  let w (n : ℕ) : ℝ :=
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)
  have hd : Summable d := summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)
  have hw : Summable w := summable_divisor_sq_log_div_rpow hδ hδ1
  have ha : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_rightMollifierCoefficient_le_sq hN δ) hd
  have ha2 : Summable (fun n => ‖a n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (norm_rightMollifierCoefficient_sq_le hN hδ) (hd.mul_left (1 / (N : ℝ)))
  have hw0 (n : ℕ) : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hn1])
  have haw : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) :=
    Summable.of_nonneg_of_le hw0 (weighted_norm_rightMollifierCoefficient_sq_le hN δ) hw
  have ha_bound : (∑' n : ℕ, ‖a n‖) ≤ 16 / δ ^ 4 :=
    (Summable.tsum_le_tsum (norm_rightMollifierCoefficient_le_sq hN δ) ha hd).trans
      (tsum_divisor_sq_div_rpow_le_pole hδ hδ1)
  have ha2_bound : (∑' n : ℕ, ‖a n‖ ^ 2) ≤ 16 / ((N : ℝ) * δ ^ 4) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (N : ℝ)) * d n :=
        Summable.tsum_le_tsum (norm_rightMollifierCoefficient_sq_le hN hδ) ha2
          (hd.mul_left _)
      _ = (1 / (N : ℝ)) * ∑' n : ℕ, d n := tsum_mul_left
      _ ≤ (1 / (N : ℝ)) * (16 / δ ^ 4) :=
        mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
      _ = _ := by ring
  have haw_bound : (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) ≤ 32 / δ ^ 5 :=
    (Summable.tsum_le_tsum (weighted_norm_rightMollifierCoefficient_sq_le hN δ) haw hw).trans
      (tsum_divisor_sq_log_div_rpow_le hδ hδ1)
  have hh := integral_logarithmicSeries_norm_sq_le a (by simp [a, rightMollifierCoefficient])
    ha ha2 haw hT
  dsimp [a] at hh
  simp_rw [logarithmicSeries_rightMollifierCoefficient hδ] at hh
  calc
    _ ≤ _ := hh
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 4 * (16 / δ ^ 4) ^ 2 + 16 * (32 / δ ^ 5) := by
      gcongr
    _ = _ := by ring

theorem integral_mollifierError_right_norm_sq_le_simple {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      2048 * (T / (N : ℝ) + 1) / δ ^ 8 := by
  have hδ4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h84 : δ ^ 8 ≤ δ ^ 4 := by
    calc
      _ = δ ^ 4 * δ ^ 4 := by ring
      _ ≤ δ ^ 4 * 1 := mul_le_mul_of_nonneg_left hδ4 (by positivity)
      _ = _ := mul_one _
  have h85 : δ ^ 8 ≤ δ ^ 5 := by
    calc
      _ = δ ^ 5 * δ ^ 3 := by ring
      _ ≤ δ ^ 5 * 1 := mul_le_mul_of_nonneg_left hδ3 (by positivity)
      _ = _ := mul_one _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h48 : 1 / δ ^ 4 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h84
  have h58 : 1 / δ ^ 5 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h85
  calc
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 :=
      integral_mollifierError_right_norm_sq_le hN hδ hδ1 hT
    _ = (16 * T / N) * (1 / δ ^ 4) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 5) := by ring
    _ ≤ (16 * T / N) * (1 / δ ^ 8) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 8) := by
      gcongr
    _ = (16 * (T / N) + 1536) / δ ^ 8 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [div_nonneg hT hN0.le]

end Sidon
