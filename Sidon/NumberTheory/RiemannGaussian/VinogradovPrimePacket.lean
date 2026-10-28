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
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace RiemannGaussian.VinogradovPrimePacket
noncomputable section
open scoped BigOperators

theorem exists_prime_packet (M R : ℕ) (hM : 0 < M) :
    ∃ P : Finset ℕ, P.card = R ∧ ∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M := by
  classical
  induction R with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ R ih =>
    obtain ⟨P, hcard, hP⟩ := ih
    obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ R * M) (by positivity)
    have hn : q ∉ P := by
      intro hqP
      exact (not_lt_of_ge (hP q hqP).2.2) hlo
    refine ⟨insert q P, by simp [hn, hcard], ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · refine ⟨hq, ?_, ?_⟩
      · have hpow : 1 ≤ 2 ^ R := Nat.one_le_two_pow
        nlinarith
      · simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi
    · obtain ⟨hprime, hMlt, hle⟩ := hP p hp
      refine ⟨hprime, hMlt, hle.trans ?_⟩
      rw [pow_succ]
      nlinarith

theorem prime_product_dvd {P : Finset ℕ} {D : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ p ∈ P, p ∣ D) : (∏ p ∈ P, p) ∣ D := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hpp := hP p (Finset.mem_insert_self p P)
    have hprime : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hpp.coprime_iff_not_dvd.mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hpp (hprime q hq)).mp hd
      exact hp (he ▸ hq)
    rw [Finset.prod_insert hp]
    exact hc.mul_dvd_of_dvd_of_dvd (hD p (Finset.mem_insert_self p P))
      (ih hprime (fun q hq => hD q (Finset.mem_insert_of_mem hq)))

theorem exists_prime_not_dvd {P : Finset ℕ} {D : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : 0 < D) (hprod : D < ∏ p ∈ P, p) :
    ∃ p ∈ P, ¬p ∣ D := by
  by_contra hn
  push Not at hn
  have hd := prime_product_dvd hP hn
  exact (not_lt_of_ge (Nat.le_of_dvd hD hd)) hprod

def separationProduct {k : ℕ} (x : Fin k → ℕ) : ℕ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, Nat.dist (x i) (x j)

theorem dist_dvd_separationProduct {k : ℕ} (x : Fin k → ℕ) {i j : Fin k} (hij : i ≠ j) :
    Nat.dist (x i) (x j) ∣ separationProduct x := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  exact (Finset.dvd_prod_of_mem (fun l : Fin k => Nat.dist (x i) (x l)) hj).trans
    (Finset.dvd_prod_of_mem (fun l : Fin k => ∏ j ∈ Finset.univ.erase l, Nat.dist (x l) (x j))
      (Finset.mem_univ i))

theorem mod_injective_of_not_dvd {k p : ℕ} (x : Fin k → ℕ)
    (hp : ¬p ∣ separationProduct x) : Function.Injective (fun i => x i % p) := by
  intro i j hij
  by_contra hne
  apply hp
  have hm : Nat.ModEq p (x i) (x j) := hij
  have hd : p ∣ Nat.dist (x i) (x j) := by
    unfold Nat.dist
    exact dvd_add hm.symm.dvd' hm.dvd'
  exact hd.trans (dist_dvd_separationProduct x hne)

end
end RiemannGaussian.VinogradovPrimePacket
