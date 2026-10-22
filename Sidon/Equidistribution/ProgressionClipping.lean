import Sidon.Equidistribution.Progressions
import Sidon.Combinatorics.Intervals

/-! # Intersecting an arithmetic progression with an integer interval -/

namespace Sidon

theorem progression_index_interval (a q : ℤ) (L N : ℕ)
    (K : Finset ℕ) (hK : K = (Finset.range L).filter (fun j : ℕ => a + q * (j : ℤ) ∈ interval N))
    (hne : K.Nonempty) : K = Finset.Icc (K.min' hne) (K.max' hne) := by
  have hlo : K.min' hne ∈ K := Finset.min'_mem K hne
  have hhi : K.max' hne ∈ K := Finset.max'_mem K hne
  have hlo' := Finset.mem_filter.mp
    (show K.min' hne ∈ (Finset.range L).filter (fun j : ℕ => a + q * (j : ℤ) ∈ interval N) by
      rw [← hK]
      exact hlo)
  have hhi' := Finset.mem_filter.mp
    (show K.max' hne ∈ (Finset.range L).filter (fun j : ℕ => a + q * (j : ℤ) ∈ interval N) by
      rw [← hK]
      exact hhi)
  obtain ⟨hlo₁, hlo₂⟩ := mem_interval.mp hlo'.2
  obtain ⟨hhi₁, hhi₂⟩ := mem_interval.mp hhi'.2
  ext j
  constructor
  · intro hj
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le K j hj, Finset.le_max' K j hj⟩
  · intro hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    rw [hK]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hjhi (Finset.mem_range.mp hhi'.1)), ?_⟩
    apply mem_interval.mpr
    have hjlo' : ((K.min' hne : ℕ) : ℤ) ≤ j := by exact_mod_cast hjlo
    have hjhi' : (j : ℤ) ≤ K.max' hne := by exact_mod_cast hjhi
    by_cases hq : 0 ≤ q
    · have h₁ := mul_le_mul_of_nonneg_left hjlo' hq
      have h₂ := mul_le_mul_of_nonneg_left hjhi' hq
      constructor <;> linarith
    · have h₁ := mul_le_mul_of_nonpos_left hjlo' (le_of_lt (lt_of_not_ge hq))
      have h₂ := mul_le_mul_of_nonpos_left hjhi' (le_of_lt (lt_of_not_ge hq))
      constructor <;> linarith

theorem image_Icc_eq_arithmeticProgression (a q : ℤ) (lo hi : ℕ) (hlo : lo ≤ hi) :
    (Finset.Icc lo hi).image (fun j : ℕ => a + q * (j : ℤ)) =
      arithmeticProgression (a + q * (lo : ℤ)) q (hi + 1 - lo) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    apply Finset.mem_image.mpr
    refine ⟨j - lo, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.cast_sub hjlo]
    ring
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨lo + j, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩, ?_⟩
    push_cast
    ring

theorem arithmeticProgression_inter_interval (a q : ℤ) (L N : ℕ) (hq : q ≠ 0) :
    ∃ b K, K ≤ N ∧ arithmeticProgression a q L ∩ interval N = arithmeticProgression b q K := by
  classical
  let J := (Finset.range L).filter (fun j : ℕ => a + q * (j : ℤ) ∈ interval N)
  have himage : arithmeticProgression a q L ∩ interval N =
      J.image (fun j : ℕ => a + q * (j : ℤ)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxP, hxN⟩ := Finset.mem_inter.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxP
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hxN⟩, rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hj, hjN⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, rfl⟩, hjN⟩
  by_cases hne : J.Nonempty
  · let lo := J.min' hne
    let hi := J.max' hne
    have hlohi : lo ≤ hi := Finset.min'_le J _ (Finset.max'_mem J hne)
    have heq : arithmeticProgression a q L ∩ interval N =
        arithmeticProgression (a + q * (lo : ℤ)) q (hi + 1 - lo) := by
      rw [himage, progression_index_interval a q L N J rfl hne]
      exact image_Icc_eq_arithmeticProgression a q lo hi hlohi
    refine ⟨a + q * (lo : ℤ), hi + 1 - lo, ?_, heq⟩
    have hcard := Finset.card_le_card
      (show arithmeticProgression a q L ∩ interval N ⊆ interval N from Finset.inter_subset_right)
    rw [heq, card_arithmeticProgression _ _ _ hq, card_interval] at hcard
    exact hcard
  · have hJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, 0, Nat.zero_le _, ?_⟩
    rw [himage, hJ]
    simp [arithmeticProgression]

end Sidon
