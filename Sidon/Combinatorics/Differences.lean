module

public import Sidon.Basic

@[expose] public section

/-! # Nonzero differences of Sidon sets -/

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {s : Set M}

/-- A nonzero difference in a Sidon set determines both endpoints. -/
theorem eq_of_sub_eq_sub (hs : IsSidonSet s) {a b c d : M}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (h : a - b = c - d) : a = c ∧ b = d := by
  have hsum := sub_eq_sub_iff_add_eq_add.mp h
  have hp := hs a d c b ha hd hc hb hsum
  have hmem : a ∈ ({c, b} : Set M) := hp ▸ Set.mem_insert a {d}
  have hac : a = c := (show a = c ∨ a = b from hmem).resolve_right hab
  rw [hac, add_right_inj] at hsum
  exact ⟨hac, hsum.symm⟩

/-- The sum and nonzero-difference definitions of a Sidon set agree. -/
theorem iff_unique_nonzero_difference : IsSidonSet s ↔
    ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      a ≠ b → a - b = c - d → a = c ∧ b = d := by
  constructor
  · intro hs a ha b hb c hc d hd hab h
    exact hs.eq_of_sub_eq_sub ha hb hc hd hab h
  · intro h a b c d ha hb hc hd hsum
    by_cases hac : a = c
    · have hbd : b = d := add_left_cancel (hac ▸ hsum)
      rw [hac, hbd]
    · have hdiff : a - c = d - b := sub_eq_sub_iff_add_eq_add.mpr
        (hsum.trans (add_comm c d))
      obtain ⟨had, hcb⟩ := h a ha c hc d hd b hb hac hdiff
      rw [had, hcb]
      exact Set.pair_comm d b

/-- Difference is injective on the ordered off-diagonal of a finite Sidon set. -/
theorem difference_injOn [DecidableEq M] {S : Finset M}
    (hS : IsSidonSet (S : Set M)) :
    Set.InjOn (fun p : M × M => p.1 - p.2) (S.offDiag : Set (M × M)) := by
  intro p hp q hq heq
  obtain ⟨hp₁, hp₂, hpne⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hq₁, hq₂, _⟩ := Finset.mem_offDiag.mp hq
  obtain ⟨h₁, h₂⟩ := hS.eq_of_sub_eq_sub hp₁ hp₂ hq₁ hq₂ hpne heq
  exact Prod.ext h₁ h₂

end IsSidonSet

namespace Sidon

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-- Ordered representations of a difference, including the diagonal at zero. -/
def differenceCount (S : Finset M) (h : M) : ℕ :=
  ((S ×ˢ S).filter fun p => p.1 - p.2 = h).card

@[simp]
theorem differenceCount_zero (S : Finset M) : differenceCount S 0 = S.card := by
  unfold differenceCount
  have hdiag : ((S ×ˢ S).filter fun p => p.1 - p.2 = 0) = S.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, sub_eq_zero, Finset.mem_diag]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ h.1⟩, h.2⟩⟩
  rw [hdiag, Finset.diag_card]

/-- Nonzero difference fibres of a Sidon set have at most one member. -/
theorem differenceCount_le_one {S : Finset M} (hS : IsSidonSet (S : Set M))
    {h : M} (hh : h ≠ 0) : differenceCount S h ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hph⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqh⟩ := Finset.mem_filter.mp hq
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
  have hpne : p.1 ≠ p.2 := by
    intro heq
    exact hh (hph.symm.trans (sub_eq_zero.mpr heq))
  obtain ⟨h₁, h₂⟩ := hS.eq_of_sub_eq_sub hp₁ hp₂ hq₁ hq₂ hpne
    (hph.trans hqh.symm)
  exact Prod.ext h₁ h₂

end Sidon
