/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Sidon.NumberTheory.RiemannGaussian.VinogradovPrimePowerRigidity

namespace RiemannGaussian.VinogradovAnisotropicCongruence
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovPrimePowerRigidity
theorem residue_class_card_le {N d q : ℕ} [NeZero N] (hd : 0 < d)
    (hN : N = d * q) (a : ℕ) :
    (Finset.univ.filter (fun x : ZMod N => x.val % d = a)).card ≤ q := by
  classical
  let S := Finset.univ.filter (fun x : ZMod N => x.val % d = a)
  have hinj : Set.InjOn (fun x : ZMod N => x.val / d) (S : Set (ZMod N)) := by
    intro x hx y hy hxy
    apply ZMod.val_injective N
    have hrx := (Finset.mem_filter.mp hx).2
    have hry := (Finset.mem_filter.mp hy).2
    change x.val / d = y.val / d at hxy
    have hx' := Nat.mod_add_div x.val d
    have hy' := Nat.mod_add_div y.val d
    rw [hrx, hxy] at hx'
    rw [hry] at hy'
    omega
  have hsub : S.image (fun x : ZMod N => x.val / d) ⊆ Finset.range q := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simpa only [hN, mul_comm d q] using x.val_lt
  calc
    S.card = (S.image (fun x : ZMod N => x.val / d)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range q).card := Finset.card_le_card hsub
    _ = q := Finset.card_range q

theorem prime_power_class_card_le {p n e : ℕ} [Fact p.Prime]
    (he : e ≤ n) (a : ℕ) :
    (Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e = a)).card ≤
      p ^ (n - e) := by
  have hp := (Fact.out : p.Prime).pos
  have : NeZero (p ^ n) := ⟨ne_of_gt (pow_pos hp n)⟩
  apply residue_class_card_le (pow_pos hp e)
  rw [← pow_add, Nat.add_sub_of_le he]

theorem nonsingular_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (residuePowerSums u i).val % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * k.factorial := by
  classical
  let T (i : Fin k) := Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e i = a i)
  have hb := nonsingular_coordinate_preimage_le hkp T
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply hb.trans
  apply Nat.mul_le_mul_right
  calc
    (∏ i, (T i).card) ≤ ∏ i, p ^ (n - e i) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      intro i hi
      exact prime_power_class_card_le (p := p) (he i) (a i)
    _ = p ^ (∑ i, (n - e i)) := Finset.prod_pow_eq_pow_sum _ _ _

theorem residuePowerSums_val {k N : ℕ} (u : Fin k → Fin N) (i : Fin k) :
    (residuePowerSums u i).val = (∑ j, (u j).val ^ (i.val + 1)) % N := by
  have he : residuePowerSums u i = ((∑ j, (u j).val ^ (i.val + 1) : ℕ) : ZMod N) := by
    simp only [residuePowerSums, Nat.cast_sum, Nat.cast_pow]
  rw [he, ZMod.val_natCast]

theorem actual_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, (u j).val ^ (i.val + 1)) % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * k.factorial := by
  have hb := nonsingular_anisotropic_card_le hkp e he a
  simp only [residuePowerSums_val] at hb
  simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow p (he _))] using hb

theorem degree_precision_cost (k b : ℕ) :
    (∑ i : Fin k, (k * b - (i.val + 1) * b)) = b * (k * (k - 1) / 2) := by
  simp_rw [← Nat.sub_mul]
  rw [← Finset.sum_mul]
  have he : (∑ i : Fin k, (k - (i.val + 1))) = k * (k - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => k - (i + 1)) k]
    simp_rw [Nat.add_comm _ 1, Nat.sub_add_eq]
    rw [Finset.sum_range_reflect (fun i => i) k, Finset.sum_range_id]
  rw [he, mul_comm]

end
end RiemannGaussian.VinogradovAnisotropicCongruence
