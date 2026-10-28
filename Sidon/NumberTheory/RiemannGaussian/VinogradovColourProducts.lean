module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Data.Nat.Prime.Factorial
public import Sidon.NumberTheory.RiemannGaussian.VinogradovDifferenceEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentPartition
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovColourProducts
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovMomentPartition RiemannGaussian.VinogradovPartitionEnergy
open RiemannGaussian.VinogradovDifferenceEnergy
def tupleLabel {ι κ : Type*} (m : ℕ) (label : ι → κ) (x : Fin m → ι) : Fin m → κ :=
  fun j => label (x j)

theorem tuple_targetWeight {ι κ : Type*} (m : ℕ) (label : ι → κ)
    (c : Fin m → κ) (x : Fin m → ι) :
    targetWeight (tupleLabel m label) (fun _ => 1) c x =
      ∏ j, targetWeight label (fun _ => 1) (c j) (x j) := by
  simp only [targetWeight, tupleLabel, funext_iff]
  by_cases hc : ∀ j, label (x j) = c j
  · simp [hc]
  · rw [ite_eq_right hc]
    obtain ⟨j, hj⟩ := not_forall.mp hc
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem tuple_class_polynomial {ι κ a : Type*} [Fintype ι] [Fintype a]
    (m : ℕ) (v : ι → a → ℤ) (label : ι → κ) (c : Fin m → κ)
    (theta : UnitAddTorus a) :
    polynomial (tupleFrequency m v) (targetWeight (tupleLabel m label) (fun _ => 1) c) theta =
      ∏ j, polynomial v (targetWeight label (fun _ => 1) (c j)) theta := by
  unfold polynomial
  simp_rw [tuple_targetWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, product_mFourier]
  rfl

theorem tuple_colour_energy {ι κ a : Type*} [Fintype ι] [Fintype κ] [Fintype a]
    (m : ℕ) (v : ι → a → ℤ) (label : ι → κ) (theta : UnitAddTorus a) :
    (∑ c : Fin m → κ, ‖polynomial (tupleFrequency m v)
      (targetWeight (tupleLabel m label) (fun _ => 1) c) theta‖ ^ 2) =
      colourEnergy label (fun i => mFourier (v i) theta) ^ m := by
  simp_rw [tuple_class_polynomial, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun _j : Fin m => fun c : κ =>
    ‖polynomial v (targetWeight label (fun _ => 1) c) theta‖ ^ 2)]
  simp only [polynomial, targetWeight, ite_mul, one_mul, zero_mul,
    colourEnergy, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem polynomial_subtype_eq {ι a : Type*} [Fintype ι] [Fintype a]
    (good : ι → Prop) [Fintype {i // good i}] (v : ι → a → ℤ) (w : ι → ℂ)
    (hw : ∀ i, ¬good i → w i = 0) (theta : UnitAddTorus a) :
    polynomial (fun i : {i // good i} => v i.val) (fun i => w i.val) theta =
      polynomial v w theta := by
  unfold polynomial
  rw [← Finset.sum_subtype (Finset.univ.filter good) (by simp) (fun i => w i * mFourier (v i) theta)]
  apply Finset.sum_subset (Finset.filter_subset good Finset.univ)
  intro i hi hn
  have hg : ¬good i := by simpa only [Finset.mem_filter, hi, true_and] using hn
  rw [hw i hg, zero_mul]

end
end RiemannGaussian.VinogradovColourProducts
