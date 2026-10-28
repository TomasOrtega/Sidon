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
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace RiemannGaussian.VinogradovPolynomialDifferencing
noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory UnitAddTorus
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullFrequency {m : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (n : ℕ) :
    (Fin d ⊕ Fin m) → ℤ := Sum.elim (fun _ => 0) (fun j => (F j).eval n)

end
end RiemannGaussian.VinogradovPolynomialDifferencing
