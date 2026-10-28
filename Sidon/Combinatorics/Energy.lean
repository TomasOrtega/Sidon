module

public import Sidon.Combinatorics.Differences
public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Tactic

@[expose] public section

/-! # The additive energy of a Sidon set -/

open scoped BigOperators

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {S : Finset M}

theorem add_eq_add_iff (hS : IsSidonSet (S : Set M)) {a b c d : M}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    a + b = c + d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have hp := hS a b c d ha hb hc hd h
    have hm : a ∈ ({c, d} : Set M) := hp ▸ Set.mem_insert a {b}
    rcases (show a = c ∨ a = d from hm) with hac | had
    · exact Or.inl ⟨hac, add_left_cancel (hac ▸ h)⟩
    · refine Or.inr ⟨had, ?_⟩
      rw [had, add_comm d b] at h
      exact add_right_cancel h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

variable [DecidableEq M]

/-- The two orders of a sum coincide exactly on the diagonal. -/
theorem addEnergy_eq (hS : IsSidonSet (S : Set M)) :
    Finset.addEnergy S S = 2 * S.card ^ 2 - S.card := by
  classical
  let A := (S ×ˢ S).image fun p => (p, p)
  let B := S.offDiag.image fun p => (p, p.swap)
  have hfilter : (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
      (fun p => p.1.1 + p.1.2 = p.2.1 + p.2.2)) = A ∪ B := by
    ext p
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    constructor
    · intro hp
      obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hab, hcd⟩ := Finset.mem_product.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
      dsimp only at ha hb hc hd heq
      rcases (hS.add_eq_add_iff ha hb hc hd).mp heq with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := h
        by_cases hab : a = b
        · subst b
          exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        rw [← heq]
        simp [ha, hb]
      · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hp
        obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
        rw [← heq]
        simp [ha, hb, add_comm]
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨p, _, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hy
    have heq : (p, p) = (q, q.swap) := hpx.trans hqx.symm
    have hpq : p = q := congrArg Prod.fst heq
    have hqq : q = q.swap := hpq ▸ congrArg Prod.snd heq
    exact (Finset.mem_offDiag.mp hq).2.2 (congrArg Prod.fst hqq)
  have hcardA : A.card = S.card * S.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_product _ _
    · intro p q h
      exact congrArg Prod.fst h
  have hcardB : B.card = S.card * S.card - S.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.offDiag_card S
    · intro p q h
      exact congrArg Prod.fst h
  rw [Finset.addEnergy_eq_card_filter, hfilter,
    Finset.card_union_of_disjoint hdisj, hcardA, hcardB, pow_two]
  have hm : S.card ≤ S.card * S.card := Nat.le_mul_self S.card
  omega

theorem addEnergy_le (hS : IsSidonSet (S : Set M)) :
    Finset.addEnergy S S ≤ 2 * S.card ^ 2 := by
  rw [hS.addEnergy_eq]
  exact Nat.sub_le _ _

theorem card_nonzero_differences (hS : IsSidonSet (S : Set M)) :
    (S.offDiag.image (fun p => p.1 - p.2)).card = S.card ^ 2 - S.card := by
  rw [Finset.card_image_of_injOn hS.difference_injOn, Finset.offDiag_card, pow_two]

theorem card_sq_sub_card_le_card_sub_one [Fintype M]
    (hS : IsSidonSet (S : Set M)) :
    S.card ^ 2 - S.card ≤ Fintype.card M - 1 := by
  have hsubset : S.offDiag.image (fun p => p.1 - p.2) ⊆
      (Finset.univ : Finset M).erase 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2,
      Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsubset
  rw [hS.card_nonzero_differences, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ] at hcard
  exact hcard

end IsSidonSet
