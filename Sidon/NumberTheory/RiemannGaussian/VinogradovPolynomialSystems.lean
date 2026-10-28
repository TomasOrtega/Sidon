module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Prime.Factorial
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCoarseCongruence
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialRigidity

@[expose] public section

namespace RiemannGaussian.VinogradovPolynomialSystems
noncomputable section
open scoped BigOperators
open Polynomial RiemannGaussian.VinogradovPolynomialRigidity RiemannGaussian.VinogradovMeanValue
def HasType {m : ℕ} (F : Fin m → ℤ[X]) (d T e : ℕ) : Prop :=
  ∀ j, (F j).natDegree = j.val + 1 ∧
    (F j).leadingCoeff = ((d + j.val + 1).descFactorial d : ℤ) * 2 ^ e * T

theorem type_leading_unit {p m d T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (n : ℕ) (j : Fin m) :
    IsUnit (((F j).leadingCoeff : ℤ) : ZMod (p ^ n)) := by
  have hp : p.Prime := Fact.out
  have hfac : ¬p ∣ (d + j.val + 1).descFactorial d := by
    intro h
    have hfull : p ∣ (d + j.val + 1).factorial := by
      rw [← Nat.factorial_mul_descFactorial (by omega : d ≤ d + j.val + 1)]
      exact dvd_mul_of_dvd_right h _
    have := hp.dvd_factorial.mp hfull
    omega
  have htwo : ¬p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < 2) h
    omega
  have hprod : ¬p ∣ (d + j.val + 1).descFactorial d * 2 ^ e * T := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact hfac h
      · exact htwo (hp.dvd_of_dvd_pow h)
    · exact hpT h
  have hcop : ((d + j.val + 1).descFactorial d * 2 ^ e * T).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr hprod).symm
  have hu := (ZMod.isUnit_iff_coprime _ (p ^ n)).mpr (hcop.pow_right n)
  simpa only [(hF j).2, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hu

theorem type_modular_regular {p m d T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (n : ℕ) :
    RegularTriangular (fun j => (F j).map (Int.castRingHom (ZMod (p ^ n)))) := by
  apply regularTriangular_map F (Int.castRingHom (ZMod (p ^ n)))
    (fun j => (hF j).1.le)
  intro j
  change IsUnit (((F j).coeff (j.val + 1) : ℤ) : ZMod (p ^ n))
  rw [← (hF j).1, coeff_natDegree]
  exact type_leading_unit hpdeg hp2 hpT hF n j

theorem type_precision_cost {m d r : ℕ} (hr : r ≤ d + m) :
    (∑ i : Fin m, (r - min (d + i.val + 1) r)) =
      (r - d) * (r - d - 1) / 2 := by
  have hterm (i : ℕ) : r - min (d + i + 1) r = (r - d) - (i + 1) := by omega
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => (r - d) - (i + 1)) m]
  have hmr : r - d ≤ m := by omega
  have hs : (∑ i ∈ Finset.range m, ((r - d) - (i + 1))) =
      ∑ i ∈ Finset.range (r - d), ((r - d) - (i + 1)) := by
    conv_lhs => rw [← Nat.add_sub_of_le hmr, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range (m - (r - d)),
        ((r - d) - (r - d + i + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      omega
    rw [hz, add_zero]
  rw [hs]
  simp_rw [Nat.add_comm _ 1, Nat.sub_add_eq]
  rw [Finset.sum_range_reflect (fun i => i) (r - d), Finset.sum_range_id]

theorem type_degree_moduli_card_le {p m d T e r : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (a : Fin m → ℕ) :
    (Finset.univ.filter (fun u : Fin m → Fin (p ^ r) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, ((F i).map (Int.castRingHom (ZMod (p ^ r)))).eval
        ((u j).val : ZMod (p ^ r))).val % p ^ min (d + i.val + 1) r = a i)).card ≤
      p ^ ((r - d) * (r - d - 1) / 2) * m.factorial := by
  have h := polynomial_anisotropic_card_le (by omega : m < p)
    (fun i => (F i).map (Int.castRingHom (ZMod (p ^ r))))
    (type_modular_regular hpdeg hp2 hpT hF r)
    (fun i => min (d + i.val + 1) r) (fun _ => Nat.min_le_right _ _) a
  simpa only [type_precision_cost hr] using h

theorem type_integer_congruence_card_le {p m d T e r : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (a : Fin m → ℤ) :
    (Finset.univ.filter (fun u : Fin m → Fin (p ^ r) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (p : ℤ) ^ min (d + i.val + 1) r ∣
        (∑ j, (F i).eval ((u j).val : ℤ)) - a i)).card ≤
      p ^ ((r - d) * (r - d - 1) / 2) * m.factorial := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have : NeZero (p ^ r) := ⟨ne_of_gt (pow_pos hp r)⟩
  apply le_trans (Finset.card_le_card ?_)
    (type_degree_moduli_card_le hpdeg hp2 hpT hr hF
      (fun i => (a i : ZMod (p ^ min (d + i.val + 1) r)).val))
  intro u hu
  obtain ⟨huprime, hueq⟩ := (Finset.mem_filter.mp hu).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
  intro i
  have hmap : (∑ j, ((F i).map (Int.castRingHom (ZMod (p ^ r)))).eval
      ((u j).val : ZMod (p ^ r))) =
      ((∑ j, (F i).eval ((u j).val : ℤ) : ℤ) : ZMod (p ^ r)) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      (Polynomial.eval_map_apply (p := F i) (Int.castRingHom (ZMod (p ^ r))) ((u j).val : ℤ))
  rw [hmap, VinogradovCoarseCongruence.intCast_reduction_val
    (pow_dvd_pow p (Nat.min_le_right _ _))]
  apply congrArg ZMod.val
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  simpa only [Nat.cast_pow] using hueq i

end
end RiemannGaussian.VinogradovPolynomialSystems
