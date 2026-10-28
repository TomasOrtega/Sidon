module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Data.List.Permutation
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue

@[expose] public section

namespace RiemannGaussian.VinogradovPowerSumRigidity
noncomputable section
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue
open scoped BigOperators

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def integerFrequency (k : ℕ) (n : ℤ) : Fin k → ℤ := fun j => n ^ (j.val + 1)

private theorem interval_frequency_eq (k N : ℕ) :
    (fun n : Fin N => integerFrequency k ((n.val : ℤ) + 1)) =
      (fun n : Fin N => monomialFrequency k (n.val + 1)) := by
  funext n j
  simp only [integerFrequency, monomialFrequency, Nat.cast_add, Nat.cast_one]

private theorem evaluated_newton {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (n : R) * (Finset.univ.val.map f).esymm n = (-1) ^ (n + 1) *
      ∑ a ∈ Finset.antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (Finset.univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f)
    (MvPolynomial.mul_esymm_eq_sum (Fin r) R n)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
    MvPolynomial.aeval_X] using h

theorem esymm_eq_of_power_sums_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {r d : ℕ} (f g : Fin r → R)
    (hchar : ∀ n, 1 ≤ n → n ≤ d → (n : R) ≠ 0)
    (h : ∀ n, 1 ≤ n → n ≤ d → (∑ i, f i ^ n) = ∑ i, g i ^ n) :
    ∀ n, n ≤ d → (Finset.univ.val.map f).esymm n =
      (Finset.univ.val.map g).esymm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n = 0
    · subst n
      simp [Multiset.esymm]
    apply mul_left_cancel₀ (hchar n (by omega) hn)
    rw [evaluated_newton, evaluated_newton]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨ha, hal⟩ := Finset.mem_filter.mp ha
    have has := Finset.mem_antidiagonal.mp ha
    rw [ih a.1 hal (by omega), h a.2 (by omega) (by omega)]

theorem multiset_eq_of_power_sums_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {r : ℕ} (f g : Fin r → R)
    (hchar : ∀ n, 1 ≤ n → n ≤ r → (n : R) ≠ 0)
    (h : ∀ n, 1 ≤ n → n ≤ r → (∑ i, f i ^ n) = ∑ i, g i ^ n) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have he := esymm_eq_of_power_sums_of_natCast_ne_zero f g hchar h
  have hp : ((Finset.univ.val.map f).map (fun t => Polynomial.X - Polynomial.C t)).prod =
      ((Finset.univ.val.map g).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [he n (by simpa using Finset.mem_range.mp hn)]
  have hr := congrArg Polynomial.roots hp
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hr

theorem multiset_eq_of_power_sums {r : ℕ} (f g : Fin r → ℤ)
    (h : ∀ n, 1 ≤ n → n ≤ r → (∑ i, f i ^ n) = ∑ i, g i ^ n) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  apply multiset_eq_of_power_sums_of_natCast_ne_zero f g _ h
  intro n hn _
  exact_mod_cast (show n ≠ 0 by omega)

theorem tuple_multiset_eq {r k : ℕ} {ι : Type*} (hrk : r ≤ k)
    (f : ι → ℤ) (hf : Function.Injective f) (x y : Fin r → ι)
    (h : (∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i))) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  apply Multiset.map_injective hf
  simp only [Multiset.map_map]
  apply multiset_eq_of_power_sums
  intro n hn hnr
  have hn1 : n - 1 + 1 = n := by omega
  have he := congrFun h ⟨n - 1, by omega⟩
  simpa only [Finset.sum_apply, integerFrequency, hn1, Function.comp_apply] using he

theorem collision_iff_perm {r k : ℕ} {ι : Type*} (hrk : r ≤ k)
    (f : ι → ℤ) (hf : Function.Injective f) (x y : Fin r → ι) :
    ((∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i))) ↔
      List.Perm (List.ofFn x) (List.ofFn y) := by
  constructor
  · intro h
    have he := tuple_multiset_eq hrk f hf x y h
    simpa only [Fin.univ_val_map, Multiset.coe_eq_coe] using he
  · intro h
    have he := (h.map (fun a : ι => integerFrequency k (f a))).sum_eq
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using he

theorem collision_fibre_le_factorial {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) (x : Fin r → ι) :
    (Finset.univ.filter (fun y : Fin r → ι =>
      (∑ i, integerFrequency k (f (x i))) =
        ∑ i, integerFrequency k (f (y i)))).card ≤ r.factorial := by
  classical
  let S := Finset.univ.filter (fun y : Fin r → ι =>
    (∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i)))
  have hsub : S.image List.ofFn ⊆ (List.ofFn x).permutations.toFinset := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl
    rw [List.mem_toFinset, List.mem_permutations]
    exact ((collision_iff_perm hrk f hf x y).mp (Finset.mem_filter.mp hy).2).symm
  calc
    S.card = (S.image List.ofFn).card :=
      (Finset.card_image_of_injective S List.ofFn_injective).symm
    _ ≤ (List.ofFn x).permutations.toFinset.card := Finset.card_le_card hsub
    _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
    _ = r.factorial := by rw [List.length_permutations, List.length_ofFn]

theorem collisionCount_le {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) :
    collisionCount r (fun i => integerFrequency k (f i)) ≤
      Fintype.card ι ^ r * r.factorial := by
  classical
  unfold VinogradovMeanValue.collisionCount
  rw [Finset.card_filter, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x : Fin r → ι, r.factorial := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [Finset.card_filter] using collision_fibre_le_factorial hrk f hf x
    _ = _ := by simp

theorem integer_moment_le {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) :
    moment r (fun i => integerFrequency k (f i)) ≤
      (Fintype.card ι : ℝ) ^ r * r.factorial := by
  rw [moment_eq_collisionCount]
  exact_mod_cast collisionCount_le hrk f hf

theorem meanValue_le {r k N : ℕ} (hrk : r ≤ k) :
    meanValue r k N ≤ (N : ℝ) ^ r * r.factorial := by
  have hf : Function.Injective (fun n : Fin N => (n.val : ℤ) + 1) := by
    intro m n h
    apply Fin.ext
    dsimp only at h
    omega
  have h := integer_moment_le hrk _ hf
  rw [interval_frequency_eq] at h
  unfold meanValue
  simpa only [Fintype.card_fin] using h

end
end RiemannGaussian.VinogradovPowerSumRigidity
