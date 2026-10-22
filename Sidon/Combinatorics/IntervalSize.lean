import Sidon.Combinatorics.Energy
import Sidon.Combinatorics.Intervals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Elementary bounds for Sidon subsets of integer intervals -/

namespace IsSidonSet

variable {N : ℕ} {S : Finset ℤ}

theorem card_le_two_mul_sqrt (hS : IsSidonSet (S : Set ℤ))
    (hSN : S ⊆ Sidon.interval N) : (S.card : ℝ) ≤ 2 * Real.sqrt N := by
  have hmN : S.card ≤ N := by
    simpa only [Sidon.card_interval] using Finset.card_le_card hSN
  by_cases hN : N = 0
  · have hm : S.card = 0 := by omega
    simp [hm, hN]
  have hsubset : S.offDiag.image (fun p => p.1 - p.2) ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp₁, hp₂, _⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨ha₁, ha₂⟩ := Sidon.mem_interval.mp (hSN hp₁)
    obtain ⟨hb₁, hb₂⟩ := Sidon.mem_interval.mp (hSN hp₂)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hI : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  have hcard := Finset.card_le_card hsubset
  rw [hS.card_nonzero_differences, hI] at hcard
  have hmSq : S.card ≤ S.card ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self S.card
  have hsq : S.card ^ 2 ≤ 4 * N := by omega
  have hsq' : (S.card : ℝ) ^ 2 ≤ 4 * (N : ℝ) := by exact_mod_cast hsq
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hnonneg := Real.sqrt_nonneg (N : ℝ)
  have hm : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  nlinarith

theorem card_le_five_mul_sqrt (hS : IsSidonSet (S : Set ℤ))
    (hSN : S ⊆ Sidon.interval N) : (S.card : ℝ) ≤ 5 * Real.sqrt N := by
  have h := hS.card_le_two_mul_sqrt hSN
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

theorem card_le_two_mul_sqrt_of_subset_Icc (hS : IsSidonSet (S : Set ℤ))
    (a : ℤ) (hSI : S ⊆ Finset.Icc (a + 1) (a + N)) :
    (S.card : ℝ) ≤ 2 * Real.sqrt N := by
  let T := S.image fun x => x - a
  have hT : IsSidonSet (T : Set ℤ) := by
    simpa only [T, Finset.coe_image, sub_eq_add_neg] using hS.image_add (-a)
  have hTN : T ⊆ Sidon.interval N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp (hSI hy)
    exact Sidon.mem_interval.mpr ⟨by omega, by omega⟩
  have hcard : T.card = S.card := by
    change (S.image (fun x => x - a)).card = S.card
    apply Finset.card_image_of_injective
    intro x y h
    change x - a = y - a at h
    omega
  simpa only [hcard] using hT.card_le_two_mul_sqrt hTN

theorem card_inter_Icc_le_two_mul_sqrt (hS : IsSidonSet (S : Set ℤ)) (a : ℤ) :
    ((S ∩ Finset.Icc (a + 1) (a + N)).card : ℝ) ≤ 2 * Real.sqrt N := by
  have hT : IsSidonSet ((S ∩ Finset.Icc (a + 1) (a + N) : Finset ℤ) : Set ℤ) :=
    hS.mono (by intro x hx; exact (Finset.mem_inter.mp hx).1)
  exact hT.card_le_two_mul_sqrt_of_subset_Icc a (Finset.inter_subset_right)

end IsSidonSet
