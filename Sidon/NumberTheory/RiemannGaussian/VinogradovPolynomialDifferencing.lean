/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Regular.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

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
