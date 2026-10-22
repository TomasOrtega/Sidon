/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovMomentPartition
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def targetWeight {ι κ : Type*} (label : ι → κ) (w : ι → ℂ) (c : κ) (i : ι) : ℂ :=
  if label i = c then w i else 0

theorem weightedShift_partition {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (label : ι → κ)
    (hlabel : ∀ i j, v i = v j → label i = label j) :
    VinogradovShiftedMoment.weightedShift v w 0 =
      ∑ c : κ, VinogradovShiftedMoment.weightedShift v
        (targetWeight label w c) 0 := by
  unfold VinogradovShiftedMoment.weightedShift targetWeight
  simp only [add_zero]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hv : v i = v j
  · have hl := hlabel i j hv
    simp [hv, hl]
  · simp [hv]

def mixedFrequency {ι : Type*} {k r : ℕ} (c : Fin k → ℤ) (tau : Fin r → ℤ)
    (x : ι → Fin k → ℤ) (u : ι → Fin r → ℤ) (z : ι) : Fin k → ℤ := fun i =>
  (∑ j, c j * x z j ^ (i.val + 1)) + ∑ j, tau j * u z j ^ (i.val + 1)

def blockSignature {ι : Type*} {q b k : ℕ} (eta : ℤ) (c : Fin k → ℤ)
    (x : ι → Fin k → ℤ) (z : ι) : (i : Fin k) → ZMod (q ^ ((i.val + 1) * b)) :=
  fun i => ((∑ j, c j * (x z j - eta) ^ (i.val + 1) : ℤ) : ZMod (q ^ ((i.val + 1) * b)))

end
end RiemannGaussian.VinogradovMomentPartition
