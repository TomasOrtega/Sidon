import Sidon.NumberTheory.BalancedMollifierSeries
import Sidon.NumberTheory.DivisorSeriesBounds

/-! # The actual mollifier detector is close to one on the line of real part two -/

noncomputable section

namespace Sidon

theorem norm_mollifierError_re_two_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : s.re = 2) :
    ‖mollifierError N s‖ ≤ 256 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hf := LSeriesHasSum_balancedMollifierCoefficient (s := s) (by rw [hs]; norm_num) N
  have hterm (n : ℕ) : ‖LSeries.term (balancedMollifierCoefficient N) s n‖ ≤
      (1 / Real.sqrt N) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    by_cases hnN : n ≤ N
    · have hz := balancedMollifierCoefficient_eq_zero hnN
      simp only [LSeries.term, hz, zero_div, ite_self, norm_zero]
      positivity
    · have hn : 0 < n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hrootle : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ n))
      have hd : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
        simpa only [pow_two] using
          (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
            exact_mod_cast Nat.le_mul_self n.divisors.card)
      have heq : (n : ℝ) ^ 2 = (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      rw [LSeries.term, if_neg (by omega : n ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hn, hs, Real.rpow_two]
      calc
        _ ≤ (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact (norm_balancedMollifierCoefficient_le hN n).trans hd
        _ ≤ (n.divisors.card : ℝ) ^ 2 /
            ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt N) := by
          rw [heq]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hrootle (Real.rpow_nonneg hn0.le _)
        _ = _ := by ring
  have hmajor := (summable_divisor_sq_div_rpow (σ := (3 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / Real.sqrt N)
  calc
    _ = ‖∑' n : ℕ, LSeries.term (balancedMollifierCoefficient N) s n‖ := by rw [hf.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (balancedMollifierCoefficient N) s n‖ :=
      norm_tsum_le_tsum_norm hf.summable.norm
    _ ≤ ∑' n : ℕ, (1 / Real.sqrt N) *
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum hterm hf.summable.norm hmajor
    _ = (1 / Real.sqrt N) *
        ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ (1 / Real.sqrt N) * 256 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := tsum_divisor_sq_div_rpow_le_pole (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at hh
      exact hh
    _ = _ := by ring

/-- A detector with square error at most one half pays at most twice that square error. -/
theorem neg_log_norm_one_sub_sq_le {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 2) :
    1 - z ^ 2 ≠ 0 ∧ -Real.log ‖1 - z ^ 2‖ ≤ 2 * ‖z‖ ^ 2 := by
  let u := ‖z‖ ^ 2
  let a := ‖1 - z ^ 2‖
  have hu0 : 0 ≤ u := sq_nonneg _
  have ha : 1 - u ≤ a := by
    have hh := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    simpa only [norm_one, norm_pow] using hh
  have ha0 : 0 < a := by dsimp [u] at *; linarith
  have hlog := Real.one_sub_inv_le_log_of_pos ha0
  have hprod : 1 ≤ (1 + 2 * u) * a := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1 + 2 * u by positivity)
    have hh' := mul_nonneg hu0 (show 0 ≤ 1 - 2 * u by dsimp [u]; linarith)
    nlinarith
  have hinv : a⁻¹ ≤ 1 + 2 * u := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ ha0).mpr (by nlinarith)
  exact ⟨norm_pos_iff.mp ha0, by change -Real.log a ≤ 2 * u; linarith⟩

/-- The center loss in Jensen's formula decays with the mollifier cutoff. -/
theorem mollifierDetector_center_bound {N : ℕ} (hN : 131072 ≤ N) {s : ℂ}
    (hs : s.re = 2) :
    mollifierDetector N s ≠ 0 ∧
      -Real.log ‖mollifierDetector N s‖ ≤ 131072 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlarge : (131072 : ℝ) ≤ N := by exact_mod_cast hN
  have herr := norm_mollifierError_re_two_le (by omega : 1 ≤ N) hs
  have hsq : ‖mollifierError N s‖ ^ 2 ≤ 65536 / (N : ℝ) := by
    have hh := sq_le_sq₀ (norm_nonneg (mollifierError N s))
      (show 0 ≤ 256 / Real.sqrt N by positivity) |>.mpr herr
    rw [div_pow, Real.sq_sqrt hNpos.le] at hh
    norm_num at hh ⊢
    exact hh
  have hhalf : ‖mollifierError N s‖ ^ 2 ≤ 1 / 2 := by
    apply hsq.trans
    exact (div_le_iff₀ hNpos).mpr (by linarith)
  obtain ⟨hne, hlog⟩ := neg_log_norm_one_sub_sq_le hhalf
  refine ⟨hne, hlog.trans ?_⟩
  calc
    2 * ‖mollifierError N s‖ ^ 2 ≤ 2 * (65536 / (N : ℝ)) := by gcongr
    _ = _ := by ring

end Sidon
