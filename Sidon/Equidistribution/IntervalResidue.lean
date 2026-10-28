module

public import Sidon.Equidistribution.LatticeCounting

@[expose] public section

/-! # Normalized interval and residue equidistribution (Corollaries 1.5 and 1.6) -/

noncomputable section

namespace Sidon

theorem reciprocal_le_sidon_error {N : ℕ} (hN : 0 < N) (S : Finset ℤ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    1 / (N : ℝ) ≤ (N : ℝ) ^ ε *
      Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    1 / (N : ℝ) = (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ (N : ℝ) ^ (-(1 / 12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNone (by norm_num)
    _ = Real.sqrt ((N : ℝ) ^ (-(1 / 6 : ℝ))) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      norm_num
    _ ≤ Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
      apply Real.sqrt_le_sqrt
      exact le_add_of_nonneg_left (abs_nonneg _)
    _ ≤ _ := le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_rpow hNone hε)

theorem sidon_normalized_progression_subset_equidistribution {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) {Q : Finset ℤ} (hQN : Q ⊆ interval N)
    (a q : ℤ) (L : ℕ) (hq : q ≠ 0) (hQ : Q = arithmeticProgression a q L)
    (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ Q).card : ℝ) / S.card - (Q.card : ℝ) / N| ≤
      (1600 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have h := sidon_normalized_progression_equidistribution hN hS hSN hm a q L hq ε hε
  rw [← hQ, Finset.inter_eq_right.mpr hQN] at h
  exact h

/-- Corollary 1.5, uniformly over both endpoint choices. -/
theorem sidon_interval_equidistribution {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (cl cr : Bool)
    (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ scaledInterval N a b cl cr).card : ℝ) / S.card - (b - a)| ≤
      (1600 * (2 + Real.log 2 + 1 / ε) + 1) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  obtain ⟨c, L, hQ⟩ := scaledInterval_is_arithmeticProgression N a b cl cr
  have hprogress := sidon_normalized_progression_subset_equidistribution hN hS hSN hm
    (scaledInterval_subset_interval hb cl cr) c 1 L one_ne_zero hQ ε hε
  have hround := normalized_scaledInterval_card_error hN ha hab cl cr
  have habsorb := reciprocal_le_sidon_error hN S ε hε.le
  calc
    _ ≤ |((S ∩ scaledInterval N a b cl cr).card : ℝ) / S.card -
        ((scaledInterval N a b cl cr).card : ℝ) / N| +
      |((scaledInterval N a b cl cr).card : ℝ) / N - (b - a)| := abs_sub_le _ _ _
    _ ≤ (1600 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) + 1 / (N : ℝ) :=
      add_le_add hprogress hround
    _ ≤ _ := by nlinarith

/-- Corollary 1.6, uniformly over all positive moduli and all residue classes. -/
theorem sidon_residue_equidistribution {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (a q : ℤ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ residueClass N a q).card : ℝ) / S.card - 1 / (q : ℝ)| ≤
      (1600 * (2 + Real.log 2 + 1 / ε) + 1) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  obtain ⟨b, L, hQ⟩ := residueClass_eq_arithmeticProgression N a q hq
  have hprogress := sidon_normalized_progression_subset_equidistribution hN hS hSN hm
    (residueClass_subset_interval N a q) b q L hq.ne' hQ ε hε
  have hround := normalized_residueClass_card_error hN a q hq
  have habsorb := reciprocal_le_sidon_error hN S ε hε.le
  calc
    _ ≤ |((S ∩ residueClass N a q).card : ℝ) / S.card -
        ((residueClass N a q).card : ℝ) / N| +
      |((residueClass N a q).card : ℝ) / N - 1 / (q : ℝ)| := abs_sub_le _ _ _
    _ ≤ (1600 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ε *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) + 1 / (N : ℝ) :=
      add_le_add hprogress hround
    _ ≤ _ := by nlinarith

end Sidon
