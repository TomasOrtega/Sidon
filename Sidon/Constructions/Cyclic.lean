import Sidon.Combinatorics.Intervals
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Lifting Sidon sets in cyclic groups to integer intervals -/

noncomputable section

open scoped Classical

namespace IsSidonSet

variable {G H : Type*} [AddCommMonoid G] [AddCommMonoid H] {A : Set G}

theorem image_addEquiv (hA : IsSidonSet A) (e : G ≃+ H) : IsSidonSet (e '' A) := by
  rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  have heq : a + b = c + d := e.injective (by simpa only [map_add] using h)
  simpa only [Set.image_pair] using congrArg (Set.image e) (hA a b c d ha hb hc hd heq)

end IsSidonSet

namespace Sidon

/-- The representatives `1,...,M` of a finite set of residues modulo `M`. -/
def liftResidues {M : ℕ} [NeZero M] (A : Finset (ZMod M)) : Finset ℤ :=
  A.image fun x => (x.val : ℤ) + 1

theorem liftResidues_subset_interval {M : ℕ} [NeZero M] (A : Finset (ZMod M)) :
    liftResidues A ⊆ interval M := by
  intro x hx
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
  rw [interval, Finset.mem_Icc]
  have hval := ZMod.val_lt a
  constructor <;> omega

theorem card_liftResidues {M : ℕ} [NeZero M] (A : Finset (ZMod M)) :
    (liftResidues A).card = A.card := by
  unfold liftResidues
  apply Finset.card_image_of_injective
  intro x y hxy
  apply ZMod.val_injective M
  change (x.val : ℤ) + 1 = (y.val : ℤ) + 1 at hxy
  exact_mod_cast add_right_cancel hxy

theorem isSidon_liftResidues {M : ℕ} [NeZero M] {A : Finset (ZMod M)}
    (hA : IsSidonSet (A : Set (ZMod M))) : IsSidonSet (liftResidues A : Set ℤ) := by
  rintro _ _ _ _ ha hb hc hd hsum
  simp only [liftResidues, Finset.mem_coe, Finset.mem_image] at ha hb hc hd
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  obtain ⟨c, hc, rfl⟩ := hc
  obtain ⟨d, hd, rfl⟩ := hd
  have heq : (a.val : ℤ) + b.val = c.val + d.val := by omega
  have hmod : a + b = c + d := by
    have h := congrArg (fun x : ℤ => (x : ZMod M)) heq
    simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] using h
  simpa only [Set.image_pair] using congrArg
    (Set.image fun x : ZMod M => (x.val : ℤ) + 1) (hA a b c d ha hb hc hd hmod)

theorem exists_integer_sidon_of_cyclic_group {G : Type*} [AddCommGroup G]
    [Fintype G] [IsAddCyclic G] (A : Finset G) (hA : IsSidonSet (A : Set G)) :
    ∃ S : Finset ℤ, S ⊆ interval (Nat.card G) ∧ S.card = A.card ∧
      IsSidonSet (S : Set ℤ) := by
  have hM : 0 < Nat.card G := Nat.card_pos
  letI : NeZero (Nat.card G) := ⟨hM.ne'⟩
  let e : ZMod (Nat.card G) ≃+ G := zmodAddCyclicAddEquiv inferInstance
  let R := A.image e.symm
  have hR : IsSidonSet (R : Set (ZMod (Nat.card G))) := by
    rw [Finset.coe_image]
    exact hA.image_addEquiv e.symm
  refine ⟨liftResidues R, liftResidues_subset_interval R, ?_, isSidon_liftResidues hR⟩
  rw [card_liftResidues, Finset.card_image_of_injective A e.symm.injective]

end Sidon
