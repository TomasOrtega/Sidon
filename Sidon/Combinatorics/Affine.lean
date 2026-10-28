module

public import Sidon.Combinatorics.Intervals

@[expose] public section

/-! # Affine images and the parity obstruction -/

namespace IsSidonSet

variable {s : Set ℤ}

/-- Multiplication by a nonzero integer preserves the Sidon property. -/
theorem image_mul (hs : IsSidonSet s) {u : ℤ} (hu : u ≠ 0) :
    IsSidonSet ((fun x => u * x) '' s) := by
  rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  have hsum : a + b = c + d := mul_left_cancel₀ hu (by simpa only [mul_add] using h)
  have hp := hs a b c d ha hb hc hd hsum
  simpa only [Set.image_pair] using
    congrArg (fun t : Set ℤ => (fun x => u * x) '' t) hp

/-- Injective integer affine images preserve the Sidon property. -/
theorem image_affine (hs : IsSidonSet s) {u : ℤ} (hu : u ≠ 0) (v : ℤ) :
    IsSidonSet ((fun x => u * x + v) '' s) := by
  simpa only [Set.image_image, Function.comp_def] using (hs.image_mul hu).image_add v

end IsSidonSet

namespace Sidon

theorem card_image_affine (S : Finset ℤ) {u : ℤ} (hu : u ≠ 0) (v : ℤ) :
    (S.image fun x => u * x + v).card = S.card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact mul_left_cancel₀ hu (add_right_cancel h)

/-- The finite construction used in Proposition 1.13. -/
def oddImage (S : Finset ℤ) : Finset ℤ := S.image fun x => 2 * x + 1

@[simp]
theorem card_oddImage (S : Finset ℤ) : (oddImage S).card = S.card :=
  card_image_affine S (by decide) 1

theorem isSidonSet_oddImage {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) :
    IsSidonSet (oddImage S : Set ℤ) := by
  simpa only [oddImage, Finset.coe_image] using hS.image_affine (by decide : (2 : ℤ) ≠ 0) 1

theorem oddImage_subset_interval {S : Finset ℤ} {N L : ℕ}
    (hL : 2 * L + 1 ≤ N) (hS : S ⊆ interval L) : oddImage S ⊆ interval N := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have ha' := mem_interval.mp (hS ha)
  apply mem_interval.mpr
  constructor <;> omega

/-- Four odd elements cannot sum to an odd element, even with repetitions. -/
theorem oddImage_no_solution (S : Finset ℤ) {a b c d e : ℤ}
    (ha : a ∈ oddImage S) (hb : b ∈ oddImage S) (hc : c ∈ oddImage S)
    (hd : d ∈ oddImage S) (he : e ∈ oddImage S) : a + b + c + d ≠ e := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
  omega

end Sidon
