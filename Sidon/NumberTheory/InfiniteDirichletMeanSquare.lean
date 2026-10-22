import Sidon.NumberTheory.LogarithmicGapMeanSquare
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Passing the uniform finite mean-square estimate to an absolutely convergent series -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Sidon

def logarithmicSeries (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a n * frequencyChar (-Real.log n) t

theorem integral_logarithmicSeries_norm_sq_le (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun n => ‖a n‖)) (ha2 : Summable (fun n => ‖a n‖ ^ 2))
    (haw : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2) ≤
      T * ∑' n : ℕ, ‖a n‖ ^ 2 + 4 * (∑' n : ℕ, ‖a n‖) ^ 2 +
        16 * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
  classical
  let S (M : ℕ) := (Finset.range M).erase 0
  let P (M : ℕ) := logarithmicPolynomial (S M) a
  have hS (M : ℕ) : ∀ n ∈ S M, 0 < n := by
    intro n hn
    have hh := Finset.mem_erase.mp hn
    omega
  have hw0 (n : ℕ) : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hn1])
  have hPnorm (M : ℕ) (t : ℝ) : ‖P M t‖ ≤ ∑' n : ℕ, ‖a n‖ := by
    calc
      _ ≤ ∑ n ∈ S M, ‖a n‖ := by
        dsimp [P, logarithmicPolynomial, finiteFrequencySum]
        exact (norm_sum_le _ _).trans_eq (by simp [norm_mul])
      _ ≤ _ := ha.sum_le_tsum (S M) (fun _ _ => norm_nonneg _)
  have hseries (t : ℝ) : Summable (fun n : ℕ => a n * frequencyChar (-Real.log n) t) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_frequencyChar, mul_one] using ha
  have hPeq (M : ℕ) (t : ℝ) : P M t = ∑ n ∈ Finset.range M,
      a n * frequencyChar (-Real.log n) t := by
    change (∑ n ∈ S M, a n * frequencyChar (-Real.log n) t) = _
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hnot
    have hn0 : n = 0 := by
      by_contra hh
      exact hnot (Finset.mem_erase.mpr ⟨hh, hn⟩)
    simp [hn0, ha0]
  have hlim (t : ℝ) : Tendsto (fun M => ‖P M t‖ ^ 2) atTop
      (𝓝 (‖logarithmicSeries a t‖ ^ 2)) := by
    simp_rw [hPeq]
    exact (hseries t).hasSum.tendsto_sum_nat.norm.pow 2
  have hint : Tendsto (fun M => ∫ t in (0 : ℝ)..T, ‖P M t‖ ^ 2) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (∑' n : ℕ, ‖a n‖) ^ 2)
    · exact Eventually.of_forall fun M =>
        ((continuous_logarithmicPolynomial (S M) a).norm.pow 2).aestronglyMeasurable
    · exact Eventually.of_forall fun M => Filter.Eventually.of_forall fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hPnorm M t) 2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => hlim t
  apply le_of_tendsto' hint
  intro M
  calc
    _ ≤ T * ∑ n ∈ S M, ‖a n‖ ^ 2 + 4 * (∑ n ∈ S M, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ S M, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) :=
      integral_logarithmicPolynomial_norm_sq_le_weighted (S M) a T (hS M)
    _ ≤ _ := by
      gcongr
      · exact ha2.sum_le_tsum (S M) (fun n _ => sq_nonneg _)
      · exact ha.sum_le_tsum (S M) (fun n _ => norm_nonneg _)
      · exact haw.sum_le_tsum (S M) (fun n _ => hw0 n)

end Sidon
