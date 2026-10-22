import Sidon.Equidistribution.ProgressionL1
import Sidon.Equidistribution.ProgressionClipping
import Sidon.FourierUniformity

/-! # Equidistribution of extremal Sidon sets in arithmetic progressions -/

noncomputable section

namespace Sidon

theorem progression_discrepancy_le_fourier_norm {N : ℕ} {S : Finset ℤ}
    (hSN : S ⊆ interval N) (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) -
        ((S.card : ℝ) / N) * (interval N ∩ arithmeticProgression a q L).card| ≤
      ‖fourierSum (discrepancyFunction N S)‖ * (2 + Real.log (N + 1)) := by
  obtain ⟨b, K, hKN, hclip⟩ := arithmeticProgression_inter_interval a q L N hq
  have hs : S ∩ arithmeticProgression b q K = S ∩ arithmeticProgression a q L := by
    rw [← hclip]
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hSN h.1⟩⟩
  have hi : interval N ∩ arithmeticProgression b q K = interval N ∩ arithmeticProgression a q L := by
    rw [← hclip]
    ext x
    simp only [Finset.mem_inter]
    tauto
  have htest := card_inter_discrepancy_le_fourierL1 S (interval N)
    (arithmeticProgression b q K) ((S.card : ℝ) / N)
  rw [hs, hi] at htest
  change _ ≤ ‖fourierSum (discrepancyFunction N S)‖ *
    fourierL1 (indicatorFinsupp (arithmeticProgression b q K)) at htest
  apply htest.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (fourierL1_arithmeticProgression_le b q K hq).trans
  apply add_le_add_left
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hKN 1

/-- A logarithmic form of Theorem 3.1, with an explicit absolute constant. -/
theorem sidon_progression_equidistribution_log {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) -
        ((S.card : ℝ) / N) * (interval N ∩ arithmeticProgression a q L).card| ≤
      16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) *
        (2 + Real.log (N + 1)) := by
  apply (progression_discrepancy_le_fourier_norm hSN a q L hq).trans
  apply mul_le_mul_of_nonneg_right _ (by
    have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith)
    linarith)
  rw [fourierSum_discrepancyFunction]
  exact sidon_fourier_uniformity hN hS hSN

theorem two_add_log_succ_le_rpow (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    2 + Real.log (N + 1) ≤ (2 + Real.log 2 + 1 / ε) * (N : ℝ) ^ ε := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNone hε.le
  have hlog₂ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    calc
      Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul (by norm_num) hNpos.ne'
  have hgrowth := Real.log_le_rpow_div hNpos.le hε
  have hconstant : 2 + Real.log 2 ≤ (2 + Real.log 2) * (N : ℝ) ^ ε :=
    le_mul_of_one_le_right (by linarith) hpow
  have hdiv : (1 / ε) * (N : ℝ) ^ ε = (N : ℝ) ^ ε / ε := by ring
  rw [add_mul, hdiv]
  linarith

/-- Theorem 3.1 for every finite integer arithmetic progression. -/
theorem sidon_progression_equidistribution {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (a q : ℤ) (L : ℕ) (hq : q ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) -
        ((S.card : ℝ) / N) * (interval N ∩ arithmeticProgression a q L).card| ≤
      (16 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ((1 / 2 : ℝ) + ε) *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  apply (sidon_progression_equidistribution_log hN hS hSN a q L hq).trans
  calc
    _ ≤ (16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)))) *
        ((2 + Real.log 2 + 1 / ε) * (N : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (two_add_log_succ_le_rpow N hN ε hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N), ← Real.sqrt_eq_rpow]
      ring

end Sidon
