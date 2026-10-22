import Sidon.Combinatorics.Affine
import Sidon.Constructions.Cyclic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # The Bose–Chowla construction from a finite field extension -/

noncomputable section

open scoped Classical

namespace Sidon.BoseChowla

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A quadratic product identity outside the base field determines an unordered pair. -/
theorem pair_eq_of_shifted_mul_eq (θ : E) (hθ : θ ∉ Set.range (algebraMap F E))
    (a b c d : F)
    (h : (θ + algebraMap F E a) * (θ + algebraMap F E b) =
      (θ + algebraMap F E c) * (θ + algebraMap F E d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  let u := a + b - c - d
  let v := a * b - c * d
  have hcoeff : θ * algebraMap F E u + algebraMap F E v = 0 := by
    dsimp [u, v]
    simp only [map_sub, map_add, map_mul]
    linear_combination h
  have hu : u = 0 := by
    by_contra hu
    have hu' : algebraMap F E u ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hu
    have heq : θ = algebraMap F E (-v / u) := by
      rw [map_div₀, map_neg]
      apply (eq_div_iff hu').mpr
      linear_combination hcoeff
    exact hθ ⟨-v / u, heq.symm⟩
  have hv : v = 0 := by
    apply (algebraMap F E).injective
    simpa only [hu, map_zero, mul_zero, zero_add] using hcoeff
  have hsum : a + b = c + d := by dsimp [u] at hu; linear_combination hu
  have hprod : a * b = c * d := sub_eq_zero.mp hv
  have hroot : (a - c) * (a - d) = 0 := by
    calc
      (a - c) * (a - d) = a ^ 2 - a * (c + d) + c * d := by ring
      _ = a ^ 2 - a * (a + b) + a * b := by rw [← hsum, ← hprod]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hroot with hac | had
  · have hac := sub_eq_zero.mp hac
    exact Or.inl ⟨hac, add_left_cancel (hac ▸ hsum)⟩
  · have had := sub_eq_zero.mp had
    refine Or.inr ⟨had, ?_⟩
    rw [had, add_comm c d] at hsum
    exact add_left_cancel hsum

theorem shifted_ne_zero (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) (x : F) :
    θ + algebraMap F E x ≠ 0 := by
  intro h
  apply hθ
  refine ⟨-x, ?_⟩
  rw [map_neg]
  linear_combination -h

def shiftedUnit (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) (x : F) : Eˣ :=
  Units.mk0 (θ + algebraMap F E x) (shifted_ne_zero θ hθ x)

theorem shiftedUnit_injective (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    Function.Injective (shiftedUnit θ hθ : F → Eˣ) := by
  intro x y h
  have h' := congrArg Units.val h
  exact (algebraMap F E).injective (add_left_cancel h')

theorem isSidon_range_shiftedUnit (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    IsSidonSet (Set.range fun x : F => Additive.ofMul (shiftedUnit θ hθ x)) := by
  rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
  have h' := congrArg (fun x : Additive Eˣ => ((Additive.toMul x : Eˣ) : E)) h
  change (θ + algebraMap F E a) * (θ + algebraMap F E b) =
    (θ + algebraMap F E c) * (θ + algebraMap F E d) at h'
  rcases pair_eq_of_shifted_mul_eq θ hθ a b c d h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Set.pair_comm _ _

variable [Fintype F]

def shiftedUnitSet (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) : Finset (Additive Eˣ) :=
  Finset.univ.image fun x : F => Additive.ofMul (shiftedUnit θ hθ x)

theorem coe_shiftedUnitSet (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (shiftedUnitSet θ hθ : Set (Additive Eˣ)) =
      Set.range fun x : F => Additive.ofMul (shiftedUnit θ hθ x) := by
  ext x
  simp only [shiftedUnitSet, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_range]

theorem card_shiftedUnitSet (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (shiftedUnitSet θ hθ).card = Fintype.card F := by
  rw [shiftedUnitSet, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · exact shiftedUnit_injective θ hθ

theorem isSidon_shiftedUnitSet (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    IsSidonSet (shiftedUnitSet θ hθ : Set (Additive Eˣ)) := by
  rw [coe_shiftedUnitSet]
  exact isSidon_range_shiftedUnit θ hθ

variable [Fintype E]

theorem exists_shift_outside_base (hcard : Fintype.card F < Fintype.card E) :
    ∃ θ : E, θ ∉ Set.range (algebraMap F E) := by
  by_contra! h
  have hsurj : Function.Surjective (algebraMap F E) := h
  exact (not_le_of_gt hcard) (Fintype.card_le_of_surjective _ hsurj)

/-- A nontrivial finite-field extension gives an integer Sidon set of base-field size. -/
theorem exists_integer_sidon (hcard : Fintype.card F < Fintype.card E) :
    ∃ S : Finset ℤ, S ⊆ interval (Fintype.card E - 1) ∧
      S.card = Fintype.card F ∧ IsSidonSet (S : Set ℤ) := by
  obtain ⟨θ, hθ⟩ := exists_shift_outside_base hcard
  obtain ⟨S, hSN, hSCard, hS⟩ := exists_integer_sidon_of_cyclic_group
    (shiftedUnitSet θ hθ) (isSidon_shiftedUnitSet θ hθ)
  have hM : Nat.card (Additive Eˣ) = Fintype.card E - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_additive, Fintype.card_units]
  refine ⟨S, ?_, hSCard.trans (card_shiftedUnitSet θ hθ), hS⟩
  simpa only [hM] using hSN

/-- The prime-field Bose–Chowla construction: `p` points in an interval of length `p²-1`. -/
theorem exists_prime_sidon (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℤ, S ⊆ interval (p ^ 2 - 1) ∧ S.card = p ∧ IsSidonSet (S : Set ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (ZMod p) < Fintype.card (GaloisField p 2) := by
    rw [ZMod.card, GaloisField.card p 2 (by norm_num)]
    nlinarith [hp.two_le]
  simpa only [ZMod.card, GaloisField.card p 2 (by norm_num)] using
    (exists_integer_sidon (F := ZMod p) (E := GaloisField p 2) hcard)

end Sidon.BoseChowla
