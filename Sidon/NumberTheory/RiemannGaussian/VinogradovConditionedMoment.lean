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
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace RiemannGaussian.VinogradovConditionedMoment
noncomputable section
open scoped BigOperators Classical
theorem translated_weighted_power_sum {r : ℕ} (c v : Fin r → ℤ) (eta : ℤ) (n : ℕ) :
    (∑ i, c i * (v i - eta) ^ n) = ∑ d ∈ Finset.range (n + 1),
      ((n.choose d : ℕ) : ℤ) * (-eta) ^ (n - d) * (∑ i, c i * v i ^ d) := by
  simp_rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end RiemannGaussian.VinogradovConditionedMoment
