import Sidon.Equidistribution.NormalizedDiscrepancy
import Sidon.Equidistribution.ProgressionEquidistribution

/-! # Normalized equidistribution in arithmetic progressions -/

noncomputable section

namespace Sidon

theorem normalized_progression_discrepancy_le_fourier_norm {N : ℕ} {S : Finset ℤ}
    (hm : 0 < S.card) (hSN : S ⊆ interval N) (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) / S.card -
      ((interval N ∩ arithmeticProgression a q L).card : ℝ) / N| ≤
      ‖fourierSum (normalizedDiscrepancy N S)‖ * (2 + Real.log (N + 1)) := by
  have hmpos : (0 : ℝ) < S.card := by exact_mod_cast hm
  have heq : ((S ∩ arithmeticProgression a q L).card : ℝ) / S.card -
      ((interval N ∩ arithmeticProgression a q L).card : ℝ) / N =
      (((S ∩ arithmeticProgression a q L).card : ℝ) -
        ((S.card : ℝ) / N) * (interval N ∩ arithmeticProgression a q L).card) / S.card := by
    field_simp
  rw [heq, abs_div, abs_of_pos hmpos,
    normalizedDiscrepancy_eq_smul_discrepancyFunction hm, fourierSum_real_smul,
    show ‖(S.card : ℝ)⁻¹ • fourierSum (discrepancyFunction N S)‖ =
      (S.card : ℝ)⁻¹ * ‖fourierSum (discrepancyFunction N S)‖ from
      (norm_smul ((S.card : ℝ)⁻¹) (fourierSum (discrepancyFunction N S))).trans
        (by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmpos)])]
  calc
    _ ≤ (‖fourierSum (discrepancyFunction N S)‖ * (2 + Real.log (N + 1))) / S.card :=
      div_le_div_of_nonneg_right (progression_discrepancy_le_fourier_norm hSN a q L hq) hmpos.le
    _ = _ := by ring

theorem sidon_normalized_progression_equidistribution_log {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) / S.card -
      ((interval N ∩ arithmeticProgression a q L).card : ℝ) / N| ≤
      1600 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) *
        (2 + Real.log (N + 1)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmnat : 0 < S.card := by
    have hpos := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
    exact_mod_cast hpos
  apply (normalized_progression_discrepancy_le_fourier_norm hmnat hSN a q L hq).trans
  apply mul_le_mul_of_nonneg_right (sidon_normalized_fourier_uniformity hN hS hSN hm)
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith)
  linarith

theorem sidon_normalized_progression_equidistribution {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (a q : ℤ) (L : ℕ) (hq : q ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) / S.card -
      ((interval N ∩ arithmeticProgression a q L).card : ℝ) / N| ≤
      (1600 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  apply (sidon_normalized_progression_equidistribution_log hN hS hSN hm a q L hq).trans
  calc
    _ ≤ (1600 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)))) *
        ((2 + Real.log 2 + 1 / ε) * (N : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (two_add_log_succ_le_rpow N hN ε hε) (by positivity)
    _ = _ := by ring

end Sidon
