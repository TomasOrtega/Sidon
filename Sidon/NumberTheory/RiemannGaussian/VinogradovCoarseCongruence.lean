/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovAnisotropicCongruence
import Sidon.NumberTheory.RiemannGaussian.VinogradovConditionedMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovSignedCongruence

namespace RiemannGaussian.VinogradovCoarseCongruence
noncomputable section
open scoped BigOperators Classical

theorem translated_power_difference_dvd {k n : ℕ} (c v u : Fin k → ℤ)
    (eta M : ℤ)
    (h : ∀ d, 1 ≤ d → d ≤ n → M ∣
      (∑ i, c i * u i ^ d) - ∑ i, c i * v i ^ d) :
    M ∣ (∑ i, c i * (u i - eta) ^ n) - ∑ i, c i * (v i - eta) ^ n := by
  rw [VinogradovConditionedMoment.translated_weighted_power_sum,
    VinogradovConditionedMoment.translated_weighted_power_sum, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro d hd
  rw [← mul_sub]
  apply dvd_mul_of_dvd_right
  by_cases hd0 : d = 0
  · subst d
    simp
  · exact h d (by omega) (by simpa using Finset.mem_range.mp hd)

theorem scaled_power_difference {k : ℕ} (c v u : Fin k → ℤ) (q : ℤ) (n : ℕ) :
    (∑ i, c i * (q * u i) ^ n) - (∑ i, c i * (q * v i) ^ n) =
      q ^ n * ((∑ i, c i * u i ^ n) - ∑ i, c i * v i ^ n) := by
  simp only [mul_pow, mul_sub, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem divide_prime_power {p m d : ℕ} (hp : p ≠ 0) (hd : d ≤ m) (x : ℤ)
    (h : (p : ℤ) ^ m ∣ (p : ℤ) ^ d * x) : (p : ℤ) ^ (m - d) ∣ x := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have he : (p : ℤ) ^ m = (p : ℤ) ^ d * (p : ℤ) ^ (m - d) := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  rw [he] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero d hpz)).mp h

theorem coarse_power_difference_dvd {p m a k n : ℕ} (hp : p ≠ 0)
    (han : a * n ≤ m) (c v u : Fin k → ℤ) (xi : ℤ)
    (h : ∀ d, 1 ≤ d → d ≤ n → (p : ℤ) ^ m ∣
      (∑ i, c i * ((p : ℤ) ^ a * u i + xi) ^ d) -
        ∑ i, c i * ((p : ℤ) ^ a * v i + xi) ^ d) :
    (p : ℤ) ^ (m - a * n) ∣ (∑ i, c i * u i ^ n) - ∑ i, c i * v i ^ n := by
  have ht := translated_power_difference_dvd c
    (fun i => (p : ℤ) ^ a * v i + xi) (fun i => (p : ℤ) ^ a * u i + xi)
    xi ((p : ℤ) ^ m) h
  simp only [add_sub_cancel_right, scaled_power_difference, ← pow_mul] at ht
  exact divide_prime_power hp han _ ht

theorem coarse_precision_cost {k a m : ℕ} (h : a * k ≤ m) :
    (∑ i : Fin k, (m - a - (m - a * (i.val + 1)))) = a * (k * (k - 1) / 2) := by
  have he (i : Fin k) : m - a - (m - a * (i.val + 1)) = a * i.val := by
    have hi : a * (i.val + 1) ≤ m :=
      (Nat.mul_le_mul_left a (by omega : i.val + 1 ≤ k)).trans h
    rw [Nat.mul_add, Nat.mul_one] at hi ⊢
    omega
  simp_rw [he]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id]

theorem coarse_complete_fibre_le {p k a m : ℕ} [Fact p.Prime] (hkp : k < p)
    (ham : a * k ≤ m) (colour : Fin k → Bool) (xi eta : ℤ) (target : Fin k → ℤ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i : Fin k,
      (p : ℤ) ^ m ∣ (∑ j, VinogradovSignedCongruence.sign (colour j) *
        ((p : ℤ) ^ a * (u j).val + xi - eta) ^ (i.val + 1)) - target i)).card ≤
      p ^ (a * (k * (k - 1) / 2)) * VinogradovSignedCongruence.colourFactorial colour := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
    Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i : Fin k,
    (p : ℤ) ^ m ∣ (∑ j, VinogradovSignedCongruence.sign (colour j) *
      ((p : ℤ) ^ a * (u j).val + xi - eta) ^ (i.val + 1)) - target i)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    obtain ⟨_, hvpower⟩ := (Finset.mem_filter.mp hv).2
    have hprec (i : Fin k) : m - a * (i.val + 1) ≤ m - a := by
      apply Nat.sub_le_sub_left
      have hi := Nat.mul_le_mul_left a (by omega : 1 ≤ i.val + 1)
      simpa only [Nat.mul_one] using hi
    have hbound := VinogradovSignedCongruence.actual_anisotropic_card_le hkp colour 0
      (fun i => m - a * (i.val + 1)) hprec
      (fun i => ∑ j, VinogradovSignedCongruence.sign (colour j) * ((v j).val : ℤ) ^ (i.val + 1))
    simp only [sub_zero, coarse_precision_cost ham] at hbound
    apply le_trans (Finset.card_le_card ?_) hbound
    intro u hu
    obtain ⟨huprime, hupower⟩ := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
    intro i
    apply coarse_power_difference_dvd (Fact.out : p.Prime).ne_zero
      ((Nat.mul_le_mul_left a (by omega : i.val + 1 ≤ k)).trans ham)
      (fun j => VinogradovSignedCongruence.sign (colour j))
      (fun j => ((v j).val : ℤ)) (fun j => ((u j).val : ℤ)) (xi - eta)
    intro d hd hdi
    let l : Fin k := ⟨d - 1, by omega⟩
    have hh := dvd_sub (hupower l) (hvpower l)
    simpa only [l, Nat.sub_add_cancel hd, sub_sub_sub_cancel_right, add_sub_assoc] using hh
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

def coarsePowerSums {p k a m : ℕ} (colour : Fin k → Bool) (xi eta : ℤ)
    (u : Fin k → Fin (p ^ (m - a))) : Fin k → ZMod (p ^ m) := fun i =>
  ((∑ j, VinogradovSignedCongruence.sign (colour j) *
    ((p : ℤ) ^ a * (u j).val + xi - eta) ^ (i.val + 1) : ℤ) : ZMod (p ^ m))

theorem coarse_modular_fibre_le {p k a m : ℕ} [Fact p.Prime] (hkp : k < p)
    (ham : a * k ≤ m) (colour : Fin k → Bool) (xi eta : ℤ)
    (target : Fin k → ZMod (p ^ m)) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      coarsePowerSums colour xi eta u = target)).card ≤
      p ^ (a * (k * (k - 1) / 2)) * VinogradovSignedCongruence.colourFactorial colour := by
  classical
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  apply le_trans (Finset.card_le_card ?_)
    (coarse_complete_fibre_le hkp ham colour xi eta (fun i => (target i).val))
  intro u hu
  obtain ⟨huprime, hupower⟩ := (Finset.mem_filter.mp hu).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
  intro i
  have hz : (((target i).val : ℤ) : ZMod (p ^ m)) =
      ((∑ j, VinogradovSignedCongruence.sign (colour j) *
        ((p : ℤ) ^ a * (u j).val + xi - eta) ^ (i.val + 1) : ℤ) : ZMod (p ^ m)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, coarsePowerSums] using
      (congrFun hupower i).symm
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ m)).mp hz
  simpa only [Nat.cast_pow] using hd

theorem coarse_preimage_le {p k a m : ℕ} [Fact p.Prime] (hkp : k < p)
    (ham : a * k ≤ m) (colour : Fin k → Bool) (xi eta : ℤ)
    (T : Finset (Fin k → ZMod (p ^ m))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      coarsePowerSums colour xi eta u ∈ T)).card ≤
      T.card * (p ^ (a * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour) := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
    Function.Injective (fun j => ((u j).val : ZMod p)))
  have he : (Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      coarsePowerSums colour xi eta u ∈ T)) =
      S.filter (fun u => coarsePowerSums colour xi eta u ∈ T) := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, ← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _ ∈ T, (p ^ (a * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour) := by
      apply Finset.sum_le_sum
      intro target htarget
      simpa only [S, Finset.filter_filter] using coarse_modular_fibre_le hkp ham colour xi eta target
    _ = _ := by simp

theorem coarse_anisotropic_card_le {p k a m : ℕ} [Fact p.Prime] (hkp : k < p)
    (ham : a * k ≤ m) (colour : Fin k → Bool) (xi eta : ℤ)
    (e : Fin k → ℕ) (he : ∀ i, e i ≤ m) (target : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (m - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i,
      (coarsePowerSums colour xi eta u i).val % p ^ e i = target i)).card ≤
      p ^ (∑ i, (m - e i)) * (p ^ (a * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour) := by
  classical
  let T (i : Fin k) := Finset.univ.filter (fun x : ZMod (p ^ m) => x.val % p ^ e i = target i)
  have hb := coarse_preimage_le hkp ham colour xi eta (Fintype.piFinset T)
  simp only [Fintype.mem_piFinset, Fintype.card_piFinset,
    T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply hb.trans
  apply Nat.mul_le_mul_right
  calc
    (∏ i, (T i).card) ≤ ∏ i, p ^ (m - e i) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      intro i hi
      exact VinogradovAnisotropicCongruence.prime_power_class_card_le (p := p) (he i) (target i)
    _ = p ^ (∑ i, (m - e i)) := Finset.prod_pow_eq_pow_sum _ _ _

theorem intCast_reduction_val {N d : ℕ} [NeZero N] (hd : d ∣ N) (z : ℤ) :
    (z : ZMod N).val % d = (z : ZMod d).val := by
  have hcast : (((z : ZMod N).val : ℕ) : ZMod d) = (z : ZMod d) := by
    rw [ZMod.natCast_val, ← ZMod.castHom_apply (h := hd)]
    exact map_intCast (ZMod.castHom hd (ZMod d)) z
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast

theorem coarse_degree_moduli_card_le {p k a b : ℕ} [Fact p.Prime] (hkp : k < p)
    (hab : a ≤ b) (colour : Fin k → Bool) (xi eta : ℤ) (target : Fin k → ℤ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (k * b - a)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i : Fin k,
      (p : ℤ) ^ ((i.val + 1) * b) ∣
        (∑ j, VinogradovSignedCongruence.sign (colour j) *
          ((p : ℤ) ^ a * (u j).val + xi - eta) ^ (i.val + 1)) - target i)).card ≤
      p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour := by
  classical
  have ham : a * k ≤ k * b := by simpa only [Nat.mul_comm a k] using Nat.mul_le_mul_left k hab
  have he (i : Fin k) : (i.val + 1) * b ≤ k * b :=
    Nat.mul_le_mul_right b (by omega : i.val + 1 ≤ k)
  have hb := coarse_anisotropic_card_le hkp ham colour xi eta
    (fun i => (i.val + 1) * b) he
    (fun i => (target i : ZMod (p ^ ((i.val + 1) * b))).val)
  rw [VinogradovAnisotropicCongruence.degree_precision_cost, ← mul_assoc,
    ← pow_add, ← Nat.add_mul, Nat.add_comm b a] at hb
  apply le_trans (Finset.card_le_card ?_) hb
  have : NeZero (p ^ (k * b)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  intro u hu
  obtain ⟨huprime, hupower⟩ := (Finset.mem_filter.mp hu).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
  intro i
  rw [coarsePowerSums, intCast_reduction_val (pow_dvd_pow p (he i))]
  apply congrArg ZMod.val
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ ((i.val + 1) * b))).mpr
  simpa only [Nat.cast_pow] using hupower i

def coarseQuotient {p a m : ℕ} [Fact p.Prime] (ha : a ≤ m)
    (x : Fin (p ^ m)) : Fin (p ^ (m - a)) :=
  ⟨x.val / p ^ a, by
    apply (Nat.div_lt_iff_lt_mul (pow_pos (Fact.out : p.Prime).pos a)).mpr
    simpa only [← pow_add, Nat.sub_add_cancel ha] using x.isLt⟩

theorem coarse_quotient_injective {p a m k : ℕ} [Fact p.Prime] (ha : a ≤ m)
    (xi : ℕ) : Set.InjOn (fun x : Fin k → Fin (p ^ m) => fun j => coarseQuotient ha (x j))
      {x | ∀ j, (x j).val % p ^ a = xi} := by
  intro x hx y hy hxy
  funext j
  apply Fin.ext
  have hq : (x j).val / p ^ a = (y j).val / p ^ a :=
    congrArg Fin.val (congrFun hxy j)
  have hrx := Nat.mod_add_div (x j).val (p ^ a)
  have hry := Nat.mod_add_div (y j).val (p ^ a)
  rw [hx j, hq] at hrx
  rw [hy j] at hry
  omega

theorem coarse_quotient_reconstruction {p a m : ℕ} [Fact p.Prime] (ha : a ≤ m)
    (xi : ℕ) (x : Fin (p ^ m)) (hx : x.val % p ^ a = xi) :
    (p : ℤ) ^ a * (coarseQuotient ha x).val + xi = (x.val : ℤ) := by
  have hnat : p ^ a * (x.val / p ^ a) + xi = x.val := by
    have h := Nat.mod_add_div x.val (p ^ a)
    rw [hx] at h
    omega
  exact_mod_cast hnat

theorem conditioned_residue_card_le {p k a b : ℕ} [Fact p.Prime] (hkp : k < p)
    (hk : 0 < k) (hab : a ≤ b) (colour : Fin k → Bool) (xi : ℕ) (eta : ℤ)
    (target : Fin k → ℤ) :
    (Finset.univ.filter (fun x : Fin k → Fin (p ^ (k * b)) =>
      (∀ j, (x j).val % p ^ a = xi) ∧
      Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p)) ∧ ∀ i : Fin k,
      (p : ℤ) ^ ((i.val + 1) * b) ∣
        (∑ j, VinogradovSignedCongruence.sign (colour j) *
          (((x j).val : ℤ) - eta) ^ (i.val + 1)) - target i)).card ≤
      p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour := by
  classical
  have ha : a ≤ k * b := by
    calc
      a ≤ b := hab
      b ≤ k * b := by simpa only [Nat.mul_comm k b] using Nat.le_mul_of_pos_right b hk
  let S := Finset.univ.filter (fun x : Fin k → Fin (p ^ (k * b)) =>
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p)) ∧ ∀ i : Fin k,
    (p : ℤ) ^ ((i.val + 1) * b) ∣
      (∑ j, VinogradovSignedCongruence.sign (colour j) *
        (((x j).val : ℤ) - eta) ^ (i.val + 1)) - target i)
  let f (x : Fin k → Fin (p ^ (k * b))) := fun j => coarseQuotient ha (x j)
  have hinj : Set.InjOn f (S : Set (Fin k → Fin (p ^ (k * b)))) :=
    (coarse_quotient_injective ha xi).mono (fun x hx => (Finset.mem_filter.mp hx).2.1)
  change S.card ≤ _
  rw [← Finset.card_image_of_injOn hinj]
  apply le_trans (Finset.card_le_card ?_)
    (coarse_degree_moduli_card_le hkp hab colour xi eta target)
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hxclass, hxprime, hxpower⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxprime, ?_⟩
  intro i
  have hrecon (j) := coarse_quotient_reconstruction ha xi (x j) (hxclass j)
  simpa only [f, hrecon] using hxpower i

end
end RiemannGaussian.VinogradovCoarseCongruence
