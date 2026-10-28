module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Vandermonde
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPowerSumRigidity

@[expose] public section

namespace RiemannGaussian.VinogradovSignedRigidity
noncomputable section
open scoped BigOperators

theorem colour_permutation_of_crossed_multiset {R : Type*} {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (hv : Function.Injective v)
    (he : Finset.univ.val.map (fun i => if colour i then v i else u i) =
      Finset.univ.val.map (fun i => if colour i then u i else v i)) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, u j = v (σ j) ∧ colour j = colour (σ j) := by
  classical
  have hex (i) : ∃ j, u j = v i ∧ colour j = colour i := by
    cases hci : colour i with
    | false =>
      have hm : v i ∈ Finset.univ.val.map (fun j => if colour j then u j else v j) :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, by simp [hci]⟩
      rw [← he] at hm
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
      cases hcj : colour j with
      | false => exact ⟨j, by simpa [hcj] using hj, by simp [hcj]⟩
      | true =>
        have hji : j = i := hv (by simpa [hcj] using hj)
        subst j
        simp_all
    | true =>
      have hm : v i ∈ Finset.univ.val.map (fun j => if colour j then v j else u j) :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, by simp [hci]⟩
      rw [he] at hm
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
      cases hcj : colour j with
      | false =>
        have hji : j = i := hv (by simpa [hcj] using hj)
        subst j
        simp_all
      | true => exact ⟨j, by simpa [hcj] using hj, by simp [hcj]⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← (hf i).1, ← (hf j).1, hij]
  let e : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e.symm, ?_⟩
  intro j
  have hj := hf (e.symm j)
  have he : f (e.symm j) = j := e.apply_symm_apply j
  simpa only [he] using hj

theorem crossed_power_sums {R : Type*} [CommRing R] {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (n : ℕ)
    (h : (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) =
      ∑ i, (if colour i then (1 : R) else -1) * u i ^ n) :
    (∑ i, (if colour i then v i else u i) ^ n) =
      ∑ i, (if colour i then u i else v i) ^ n := by
  apply sub_eq_zero.mp
  calc
    _ = (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) -
        ∑ i, (if colour i then (1 : R) else -1) * u i ^ n := by
      simp only [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      cases colour i <;> simp
      ring
    _ = 0 := by rw [h, sub_self]

theorem signed_power_permutation {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (hv : Function.Injective v)
    (hchar : ∀ n, 1 ≤ n → n ≤ k → (n : R) ≠ 0)
    (h : ∀ n, 1 ≤ n → n ≤ k →
      (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) =
      ∑ i, (if colour i then (1 : R) else -1) * u i ^ n) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, u j = v (σ j) ∧ colour j = colour (σ j) := by
  apply colour_permutation_of_crossed_multiset colour v u hv
  apply VinogradovPowerSumRigidity.multiset_eq_of_power_sums_of_natCast_ne_zero
      _ _ hchar
  intro n hn hnk
  exact crossed_power_sums colour v u n (h n hn hnk)

abbrev PreservingPerm {ι : Type*} (P : ι → Prop) :=
  {σ : Equiv.Perm ι // ∀ i, P (σ i) ↔ P i}

def preservingPermEquiv {ι : Type*} (P : ι → Prop) [DecidablePred P] :
    PreservingPerm P ≃ (Equiv.Perm {i // P i} × Equiv.Perm {i // ¬ P i}) where
  toFun σ := (σ.val.subtypePerm σ.property,
    σ.val.subtypePerm (fun i => not_congr (σ.property i)))
  invFun pair := ⟨pair.1.subtypeCongr pair.2, by
    intro i
    by_cases hi : P i
    · simp only [hi, iff_true]
      rw [Equiv.Perm.subtypeCongr.left_apply _ _ hi]
      exact (pair.1 ⟨i, hi⟩).property
    · simp only [hi, iff_false]
      rw [Equiv.Perm.subtypeCongr.right_apply _ _ hi]
      exact (pair.2 ⟨i, hi⟩).property⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : P i
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hi]
      rfl
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hi]
      rfl
  right_inv pair := by
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.left_apply_subtype]
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.right_apply_subtype]

theorem card_preservingPerm {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    Nat.card (PreservingPerm P) =
      (Fintype.card {i // P i}).factorial * (Fintype.card {i // ¬ P i}).factorial := by
  classical
  rw [Nat.card_congr (preservingPermEquiv P), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]

end
end RiemannGaussian.VinogradovSignedRigidity
