module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems

@[expose] public section

namespace RiemannGaussian.VinogradovBinomialRows
noncomputable section
open scoped BigOperators Classical
open Polynomial RiemannGaussian.VinogradovPolynomialSystems
def row {R : Type*} [CommRing R] (c : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : R) * c ^ (n - j) * f j

theorem row_split {R : Type*} [CommRing R] (c : R) (f : ℕ → R) (n : ℕ) :
    row c f n = (∑ j ∈ Finset.range n, (n.choose j : R) * c ^ (n - j) * f j) + f n := by
  simp only [row, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self,
    pow_zero, Nat.cast_one, one_mul]

theorem row_zero_iff {R : Type*} [CommRing R] (c : R) (f : ℕ → R) (k : ℕ) :
    (∀ n, n ≤ k → row c f n = 0) ↔ ∀ n, n ≤ k → f n = 0 := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have he := h n hn
      rw [row_split] at he
      have hz : (∑ j ∈ Finset.range n, (n.choose j : R) * c ^ (n - j) * f j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        rw [ih j hjn (hjn.le.trans hn), mul_zero]
      simpa only [hz, zero_add] using he
  · intro h n hn
    unfold row
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [h j (hjn.trans hn), mul_zero]

theorem row_add {R : Type*} [CommRing R] (c : R) (f g : ℕ → R) (n : ℕ) :
    row c (fun j => f j + g j) n = row c f n + row c g n := by
  simp only [row, mul_add, Finset.sum_add_distrib]

theorem row_sub {R : Type*} [CommRing R] (c : R) (f g : ℕ → R) (n : ℕ) :
    row c (fun j => f j - g j) n = row c f n - row c g n := by
  simp only [row, mul_sub, Finset.sum_sub_distrib]

theorem row_eq_iff {R : Type*} [CommRing R] (c : R) (f g : ℕ → R) (k : ℕ) :
    (∀ n, n ≤ k → row c f n = row c g n) ↔ ∀ n, n ≤ k → f n = g n := by
  simpa only [row_sub, sub_eq_zero] using row_zero_iff c (fun n => f n - g n) k

theorem row_sum {R ι : Type*} [CommRing R] (c : R) (S : Finset ι)
    (f : ι → ℕ → R) (n : ℕ) :
    row c (fun j => ∑ i ∈ S, f i j) n = ∑ i ∈ S, row c (f i) n := by
  simp only [row, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem row_pow {R : Type*} [CommRing R] (c x : R) (n : ℕ) :
    row c (fun j => x ^ j) n = (x + c) ^ n := by
  rw [row, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem map_row {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (c : R) (f : ℕ → R) (n : ℕ) :
    g (row c f n) = row (g c) (fun j => g (f j)) n := by
  simp only [row, map_sum, map_mul, map_natCast, map_pow]

def fullSystem {m : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (n : ℕ) : ℤ[X] :=
  if h : d < n ∧ n ≤ d + m then F ⟨n - d - 1, by omega⟩ else 0

theorem fullSystem_low {m d n : ℕ} (F : Fin m → ℤ[X]) (hn : n ≤ d) :
    fullSystem d F n = 0 := by
  unfold fullSystem
  exact dite_eq_right (by omega)

theorem fullSystem_active {m : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (i : Fin m) :
    fullSystem d F (d + i.val + 1) = F i := by
  unfold fullSystem
  rw [dite_eq_left (by have := i.isLt; omega)]
  congr 1
  apply Fin.ext
  change d + i.val + 1 - d - 1 = i.val
  omega

def rowSystem {m : ℕ} (d : ℕ) (c : ℤ) (F : Fin m → ℤ[X]) : Fin m → ℤ[X] :=
  fun i => row (C c) (fullSystem d F) (d + i.val + 1)

theorem polynomial_row (c : ℤ) (F : ℕ → ℤ[X]) (n : ℕ) :
    row (C c) F n = ∑ j ∈ Finset.range (n + 1), C ((n.choose j : ℤ) * c ^ (n - j)) * F j := by
  simp only [row, map_mul, map_natCast, map_pow]

theorem fullSystem_rowSystem {m : ℕ} (d : ℕ) (c : ℤ) (F : Fin m → ℤ[X])
    {n : ℕ} (hn : n ≤ d + m) :
    fullSystem d (rowSystem d c F) n = row (C c) (fullSystem d F) n := by
  by_cases hdn : d < n
  · let i : Fin m := ⟨n - d - 1, by omega⟩
    have he : n = d + i.val + 1 := by dsimp [i]; omega
    rw [he, fullSystem_active]
    rfl
  · rw [fullSystem_low _ (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [fullSystem_low F (by have := Finset.mem_range.mp hj; omega), mul_zero]

theorem row_degree_leading (c : ℤ) (F : ℕ → ℤ[X]) (n : ℕ)
    (hpos : 0 < (F n).natDegree)
    (hdeg : ∀ j, j < n → (F j).natDegree < (F n).natDegree) :
    (row (C c) F n).natDegree = (F n).natDegree ∧
      (row (C c) F n).leadingCoeff = (F n).leadingCoeff := by
  rw [polynomial_row, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, map_one]
  let S := ∑ j ∈ Finset.range n, C ((n.choose j : ℤ) * c ^ (n - j)) * F j
  have hs : S.natDegree ≤ (F n).natDegree - 1 := by
    apply (natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro j hj
    apply (natDegree_C_mul_le _ _).trans
    have := hdeg j (Finset.mem_range.mp hj)
    omega
  have hlt : S.natDegree < (F n).natDegree := by omega
  exact ⟨natDegree_add_eq_right_of_natDegree_lt hlt,
    leadingCoeff_add_of_degree_lt (degree_lt_degree hlt)⟩

theorem hasType_rowSystem {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) (c : ℤ) : HasType (rowSystem d c F) d T e := by
  intro i
  have hp : 0 < (fullSystem d F (d + i.val + 1)).natDegree := by
    rw [fullSystem_active, (hF i).1]
    omega
  have hd (j : ℕ) (hj : j < d + i.val + 1) :
      (fullSystem d F j).natDegree < (fullSystem d F (d + i.val + 1)).natDegree := by
    rw [fullSystem_active, (hF i).1]
    by_cases hjd : j ≤ d
    · rw [fullSystem_low F hjd, natDegree_zero]
      omega
    · let l : Fin m := ⟨j - d - 1, by have := i.isLt; omega⟩
      have he : j = d + l.val + 1 := by dsimp [l]; omega
      rw [he, fullSystem_active, (hF l).1]
      dsimp [l]
      omega
  have he := row_degree_leading c (fullSystem d F) (d + i.val + 1) hp hd
  simp only [fullSystem_active] at he
  exact ⟨he.1.trans (hF i).1, he.2.trans (hF i).2⟩

end
end RiemannGaussian.VinogradovBinomialRows
