/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

namespace RiemannGaussian.VinogradovCongruenceEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open UnitAddTorus
theorem sum_energy_le_card_mul {α : Type*} (S : Finset α) (w : α → ℂ) :
    ‖∑ x ∈ S, w x‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖w x‖ ^ 2 := by
  have hn := norm_sum_le S w
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun x => ‖w x‖)
  calc
    ‖∑ x ∈ S, w x‖ ^ 2 ≤ (∑ x ∈ S, ‖w x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (S.card : ℝ) * ∑ x ∈ S, ‖w x‖ ^ 2 := by simpa using hc

end
end RiemannGaussian.VinogradovCongruenceEnergy
