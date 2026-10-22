/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Vandermonde
import Sidon.NumberTheory.RiemannGaussian.VinogradovPowerSumRigidity

namespace RiemannGaussian.VinogradovPrimePowerRigidity
noncomputable section
open scoped BigOperators

def powerJacobian {R : Type*} [CommRing R] {k : ℕ} (v : Fin k → R) :
    Matrix (Fin k) (Fin k) R := fun i j => ((i.val + 1 : ℕ) : R) * v j ^ i.val

theorem determinant_ne_zero {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (v : Fin k → R) (hv : Function.Injective v)
    (hchar : ∀ i : Fin k, ((i.val + 1 : ℕ) : R) ≠ 0) :
    (powerJacobian v).det ≠ 0 := by
  have he : powerJacobian v = Matrix.of (fun i j =>
      ((i.val + 1 : ℕ) : R) * (Matrix.vandermonde v).transpose i j) := rfl
  rw [he, Matrix.det_mul_column, Matrix.det_transpose]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hchar i))
    (Matrix.det_vandermonde_ne_zero_iff.mpr hv)

theorem prime_determinant_ne_zero {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v : Fin k → ZMod p) (hv : Function.Injective v) :
    (powerJacobian v).det ≠ 0 := by
  apply determinant_ne_zero v hv
  intro i hi
  have hd := (ZMod.natCast_eq_zero_iff (i.val + 1) p).mp hi
  have hp := Nat.le_of_dvd (by omega : 0 < i.val + 1) hd
  omega

theorem prime_linearized_injective {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v : Fin k → ZMod p) (hv : Function.Injective v) (w : Fin k → ZMod p)
    (h : ∀ i : Fin k, ∑ j, ((i.val + 1 : ℕ) : ZMod p) * v j ^ i.val * w j = 0) :
    w = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (prime_determinant_ne_zero hkp v hv)
  ext i
  exact h i

theorem power_remainder (x q w : ℤ) (n : ℕ) :
    ∃ E : ℤ, (x + q * w) ^ (n + 1) =
      x ^ (n + 1) + (n + 1) * x ^ n * q * w + q ^ 2 * E := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨(n + 1) * x ^ n * w ^ 2 + E * x + q * E * w, ?_⟩
    rw [pow_succ (x + q * w) (n + 1), hE]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem sum_power_remainder {k : ℕ} (v w : Fin k → ℤ) (q : ℤ) (n : ℕ) :
    ∃ E : ℤ, (∑ j, (v j + q * w j) ^ (n + 1)) =
      (∑ j, v j ^ (n + 1)) + q * (∑ j, (n + 1) * v j ^ n * w j) + q ^ 2 * E := by
  choose E hE using fun j => power_remainder (v j) q (w j) n
  refine ⟨∑ j, E j, ?_⟩
  simp_rw [hE]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem linearized_divisibility {k : ℕ} (v w : Fin k → ℤ) {p q : ℤ}
    (hq : q ≠ 0) (hpq : p ∣ q) (n : ℕ)
    (h : p * q ∣ (∑ j, (v j + q * w j) ^ (n + 1)) - ∑ j, v j ^ (n + 1)) :
    p ∣ ∑ j, (n + 1) * v j ^ n * w j := by
  obtain ⟨E, hE⟩ := sum_power_remainder v w q n
  have he : (∑ j, (v j + q * w j) ^ (n + 1)) - (∑ j, v j ^ (n + 1)) =
      q * ((∑ j, (n + 1) * v j ^ n * w j) + q * E) := by
    rw [hE]
    ring
  rw [he, mul_comm p q] at h
  have hc : p ∣ (∑ j, (n + 1) * v j ^ n * w j) + q * E :=
    (mul_dvd_mul_iff_left hq).mp h
  have ht : p ∣ q * E := dvd_mul_of_dvd_left hpq E
  simpa only [add_sub_cancel_right] using dvd_sub hc ht

theorem prime_lift_increment {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v w : Fin k → ℤ) {q : ℤ} (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hv : Function.Injective (fun i => (v i : ZMod p)))
    (h : ∀ i : Fin k, (p : ℤ) * q ∣
      (∑ j, (v j + q * w j) ^ (i.val + 1)) - ∑ j, v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) ∣ w j := by
  have hlin (i : Fin k) := linearized_divisibility v w hq hpq i.val (h i)
  have hzero : (fun j => (w j : ZMod p)) = 0 := by
    apply prime_linearized_injective hkp (fun i => (v i : ZMod p)) hv
    intro i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hlin i)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Int.cast_pow, Nat.cast_add, Nat.cast_one] using hz
  intro j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  exact congrFun hzero j

theorem prime_lift_step {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v u : Fin k → ℤ) {q : ℤ} (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hv : Function.Injective (fun i => (v i : ZMod p)))
    (hcoarse : ∀ j, q ∣ u j - v j)
    (hpowers : ∀ i : Fin k, (p : ℤ) * q ∣
      (∑ j, u j ^ (i.val + 1)) - ∑ j, v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) * q ∣ u j - v j := by
  choose w hw using hcoarse
  have hu (j) : u j = v j + q * w j := by linarith [hw j]
  have hlift := prime_lift_increment hkp v w hq hpq hv
    (by simpa only [← hu] using hpowers)
  intro j
  obtain ⟨a, ha⟩ := hlift j
  refine ⟨a, ?_⟩
  rw [hw j, ha]
  ring

theorem prime_power_rigidity {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v u : Fin k → ℤ) (hv : Function.Injective (fun i => (v i : ZMod p)))
    (hfirst : ∀ j, (p : ℤ) ∣ u j - v j) (n : ℕ)
    (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, u j ^ (i.val + 1)) - ∑ j, v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) ^ n ∣ u j - v j := by
  induction n with
  | zero => intro j; simp
  | succ n ih =>
    by_cases hn : n = 0
    · simpa only [hn, zero_add, pow_one] using hfirst
    have hp : (p : ℤ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hcoarse := ih (fun i => dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) (hpowers i))
    have hnext := prime_lift_step hkp v u (pow_ne_zero n hp)
      (dvd_pow_self (p : ℤ) hn) hv hcoarse
      (by simpa only [pow_succ, mul_comm] using hpowers)
    simpa only [pow_succ, mul_comm] using hnext

theorem prime_multiset_eq {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v u : Fin k → ZMod p)
    (h : ∀ i : Fin k, (∑ j, v j ^ (i.val + 1)) = ∑ j, u j ^ (i.val + 1)) :
    Finset.univ.val.map v = Finset.univ.val.map u := by
  apply VinogradovPowerSumRigidity.multiset_eq_of_power_sums_of_natCast_ne_zero v u
  · intro n hn hnk hz
    have hd := (ZMod.natCast_eq_zero_iff n p).mp hz
    have hp := Nat.le_of_dvd (by omega : 0 < n) hd
    omega
  · intro n hn hnk
    have he := h ⟨n - 1, by omega⟩
    simpa only [Nat.sub_add_cancel hn] using he

theorem exists_perm_of_multiset_eq {R : Type*} {k : ℕ} (v u : Fin k → R)
    (hv : Function.Injective v) (he : Finset.univ.val.map v = Finset.univ.val.map u) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, v (σ j) = u j := by
  classical
  have hu : Function.Injective u := by
    have hs : (Finset.univ.val.map u).Nodup := by
      rw [← he]
      exact Finset.univ.nodup.map hv
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hs i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  have hex (j) : ∃ i, v i = u j := by
    have hm : u j ∈ Finset.univ.val.map u := Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    rw [← he] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, hi⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply hu
    rw [← hf i, ← hf j, hij]
  exact ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, hf⟩

theorem prime_power_permutation {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (v u : Fin k → ℤ) (hv : Function.Injective (fun i => (v i : ZMod p)))
    (n : ℕ) (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, u j ^ (i.val + 1)) - ∑ j, v j ^ (i.val + 1)) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, (p : ℤ) ^ n ∣ u j - v (σ j) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨Equiv.refl _, by simp⟩
  have he := prime_multiset_eq hkp (fun j => (v j : ZMod p)) (fun j => (u j : ZMod p)) (by
    intro i
    have hd := dvd_trans (dvd_pow_self (p : ℤ) hn) (hpowers i)
    have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr hd
    simpa only [Int.cast_sum, Int.cast_pow] using hz)
  obtain ⟨σ, hσ⟩ := exists_perm_of_multiset_eq _ _ hv he
  refine ⟨σ, prime_power_rigidity hkp (fun j => v (σ j)) u (hv.comp σ.injective) ?_ n ?_⟩
  · intro j
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp (hσ j)
  · intro i
    rw [Equiv.sum_comp σ (fun j => v j ^ (i.val + 1))]
    exact hpowers i

theorem residue_tuple_permutation {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (v u : Fin k → Fin (p ^ n))
    (hv : Function.Injective (fun i => ((v i).val : ZMod p)))
    (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, ((u j).val : ℤ) ^ (i.val + 1)) - ∑ j, ((v j).val : ℤ) ^ (i.val + 1)) :
    ∃ σ : Equiv.Perm (Fin k), u = fun j => v (σ j) := by
  obtain ⟨σ, hσ⟩ := prime_power_permutation hkp
    (fun j => ((v j).val : ℤ)) (fun j => ((u j).val : ℤ))
    (by simpa only [Int.cast_natCast] using hv) n hpowers
  refine ⟨σ, ?_⟩
  funext j
  apply Fin.ext
  have hd : ((p ^ n : ℕ) : ℤ) ∣ ((u j).val : ℤ) - ((v (σ j)).val : ℤ) := by
    simpa only [Nat.cast_pow] using hσ j
  have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ n)).mpr hd
  have he := congrArg ZMod.val hz
  simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt (v (σ j)).isLt,
    ZMod.val_natCast_of_lt (u j).isLt] using he.symm

theorem residue_fibre_le_factorial {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (v : Fin k → Fin (p ^ n))
    (hv : Function.Injective (fun i => ((v i).val : ZMod p))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) => ∀ i : Fin k,
      (p : ℤ) ^ n ∣ (∑ j, ((u j).val : ℤ) ^ (i.val + 1)) -
        ∑ j, ((v j).val : ℤ) ^ (i.val + 1))).card ≤ k.factorial := by
  classical
  have hsub : (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) => ∀ i : Fin k,
      (p : ℤ) ^ n ∣ (∑ j, ((u j).val : ℤ) ^ (i.val + 1)) -
        ∑ j, ((v j).val : ℤ) ^ (i.val + 1))) ⊆
      Finset.univ.image (fun σ : Equiv.Perm (Fin k) => fun j => v (σ j)) := by
    intro u hu
    obtain ⟨σ, hσ⟩ := residue_tuple_permutation hkp v u hv (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ.symm⟩
  exact (Finset.card_le_card hsub).trans (by simpa [Fintype.card_perm] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin k) => fun j => v (σ j))))

def residuePowerSums {k N : ℕ} (u : Fin k → Fin N) : Fin k → ZMod N :=
  fun i => ∑ j, ((u j).val : ZMod N) ^ (i.val + 1)

theorem nonsingular_fibre_le_factorial {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ZMod (p ^ n)) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residuePowerSums u = target)).card ≤ k.factorial := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)) ∧ residuePowerSums u = target)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    obtain ⟨hvprime, hvpower⟩ := (Finset.mem_filter.mp hv).2
    apply le_trans (Finset.card_le_card ?_) (residue_fibre_le_factorial hkp v hvprime)
    intro u hu
    obtain ⟨_, hupower⟩ := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i
    have he := congrFun (hvpower.trans hupower.symm) i
    have hz : ((∑ j, ((v j).val : ℤ) ^ (i.val + 1) : ℤ) : ZMod (p ^ n)) =
        ((∑ j, ((u j).val : ℤ) ^ (i.val + 1) : ℤ) : ZMod (p ^ n)) := by
      simpa only [residuePowerSums, Int.cast_sum, Int.cast_pow, Int.cast_natCast] using he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ n)).mp hz
    simpa only [Nat.cast_pow] using hd
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

theorem nonsingular_preimage_le {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (T : Finset (Fin k → ZMod (p ^ n))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residuePowerSums u ∈ T)).card ≤ T.card * k.factorial := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)))
  have he : (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residuePowerSums u ∈ T)) = S.filter (fun u => residuePowerSums u ∈ T) := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, ← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _ ∈ T, k.factorial := by
      apply Finset.sum_le_sum
      intro target htarget
      simpa only [S, Finset.filter_filter] using nonsingular_fibre_le_factorial hkp target
    _ = _ := by simp

theorem nonsingular_coordinate_preimage_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (T : Fin k → Finset (ZMod (p ^ n))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, residuePowerSums u i ∈ T i)).card ≤ (∏ i, (T i).card) * k.factorial := by
  simpa only [Fintype.mem_piFinset, Fintype.card_piFinset] using
    nonsingular_preimage_le hkp (Fintype.piFinset T)

end
end RiemannGaussian.VinogradovPrimePowerRigidity
