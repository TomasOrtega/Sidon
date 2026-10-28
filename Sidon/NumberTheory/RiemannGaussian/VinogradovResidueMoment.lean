module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovResidueMoment
noncomputable section
open scoped BigOperators

theorem differenceCount_map_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (f : ι → κ) (hf : Function.Injective f) (v : κ → d → ℤ) (h : d → ℤ) :
    VinogradovShiftedMoment.differenceCount (fun i => v (f i)) h ≤
      VinogradovShiftedMoment.differenceCount v h := by
  classical
  unfold VinogradovShiftedMoment.differenceCount
  apply Finset.card_le_card_of_injOn (fun xy => (f xy.1, f xy.2))
  · intro xy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2⟩
  · intro xy hxy uv huv he
    exact Prod.ext (hf (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))

abbrev ResidueWindow (q xi X : ℕ) := {n : Fin X // (n.val + 1) % q = xi}

def residueQuotient {q xi X : ℕ} (x : ResidueWindow q xi X) : Fin (X / q + 1) :=
  ⟨(x.val.val + 1) / q, by
    have h := Nat.div_le_div_right (show x.val.val + 1 ≤ X by omega) (c := q)
    omega⟩

theorem residueQuotient_injective {q xi X : ℕ} :
    Function.Injective (residueQuotient (q := q) (xi := xi) (X := X)) := by
  intro x y hxy
  apply Subtype.ext
  apply Fin.ext
  have hq := congrArg Fin.val hxy
  change (x.val.val + 1) / q = (y.val.val + 1) / q at hq
  have hx := Nat.mod_add_div (x.val.val + 1) q
  have hy := Nat.mod_add_div (y.val.val + 1) q
  rw [x.property, hq] at hx
  rw [y.property] at hy
  omega

theorem residue_reconstruction {q xi X : ℕ} (x : ResidueWindow q xi X) :
    (q : ℤ) * (((residueQuotient x).val + 1 : ℕ) : ℤ) + ((xi : ℤ) - q) =
      ((x.val.val + 1 : ℕ) : ℤ) := by
  have hn := Nat.mod_add_div (x.val.val + 1) q
  rw [x.property] at hn
  have hz : (xi : ℤ) + (q : ℤ) * (residueQuotient x).val =
      ((x.val.val + 1 : ℕ) : ℤ) := by exact_mod_cast hn
  push_cast
  push_cast at hz
  linarith

end
end RiemannGaussian.VinogradovResidueMoment
