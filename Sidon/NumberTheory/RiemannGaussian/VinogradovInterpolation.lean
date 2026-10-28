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
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace RiemannGaussian.VinogradovInterpolation
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_geometric_le {d : Type*} [Fintype d]
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (f g : UnitAddTorus d → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ theta, 0 ≤ f theta) (hg0 : ∀ theta, 0 ≤ g theta) :
    (∫ theta, f theta ^ t * g theta ^ (1 - t)) ≤
      (∫ theta, f theta) ^ t * (∫ theta, g theta) ^ (1 - t) := by
  have ht' : 0 < 1 - t := by linarith
  have hpq : (1 / t).HolderConjugate (1 / (1 - t)) := by
    constructor
    · simp
    · positivity
    · positivity
  have hfc := hf.rpow_const (fun _ => Or.inr ht.le)
  have hgc := hg.rpow_const (fun _ => Or.inr ht'.le)
  have he := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (Filter.Eventually.of_forall (fun theta => Real.rpow_nonneg (hf0 theta) _))
    (Filter.Eventually.of_forall (fun theta => Real.rpow_nonneg (hg0 theta) _))
    (hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hgc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hff (theta) : (f theta ^ t) ^ (1 / t) = f theta := by
    rw [← Real.rpow_mul (hf0 theta), mul_one_div_cancel ht.ne', Real.rpow_one]
  have hgg (theta) : (g theta ^ (1 - t)) ^ (1 / (1 - t)) = g theta := by
    rw [← Real.rpow_mul (hg0 theta), mul_one_div_cancel ht'.ne', Real.rpow_one]
  simpa only [hff, hgg, one_div_one_div] using he

end
end RiemannGaussian.VinogradovInterpolation
