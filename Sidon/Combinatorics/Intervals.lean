module

public import Sidon.Combinatorics.Differences
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! # Integer intervals and elementary invariances -/

namespace Sidon

/-- The paper's interval `[N]`, as a finite set of integers. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 N

@[simp]
theorem mem_interval {N : ℕ} {x : ℤ} :
    x ∈ interval N ↔ 1 ≤ x ∧ x ≤ N := Finset.mem_Icc

@[simp]
theorem card_interval (N : ℕ) : (interval N).card = N := by
  simp [interval, Int.card_Icc]

@[simp]
theorem interval_zero : interval 0 = ∅ := by
  simp [interval]

end Sidon

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {s t : Set M}

/-- Restricting a Sidon set preserves uniqueness of sums. -/
theorem mono (hs : IsSidonSet s) (ht : t ⊆ s) : IsSidonSet t :=
  fun a b c d ha hb hc hd => hs a b c d (ht ha) (ht hb) (ht hc) (ht hd)

/-- Translation preserves the Sidon property. -/
theorem image_add (hs : IsSidonSet s) (v : M) :
    IsSidonSet ((fun x => x + v) '' s) := by
  rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  have hsum : a + b = c + d := by
    apply add_right_cancel (b := v + v)
    simpa only [add_assoc, add_left_comm, add_comm] using h
  have hp := hs a b c d ha hb hc hd hsum
  simpa only [Set.image_pair] using
    congrArg (fun u : Set M => (fun x => x + v) '' u) hp

end IsSidonSet
