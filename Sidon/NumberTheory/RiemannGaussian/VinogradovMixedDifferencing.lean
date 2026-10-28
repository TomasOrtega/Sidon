module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.MeanInequalitiesPow
public import Sidon.NumberTheory.RiemannGaussian.VinogradovDifferenceEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy

@[expose] public section

namespace RiemannGaussian.VinogradovMixedDifferencing
noncomputable section
open scoped BigOperators
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovPartitionEnergy
open RiemannGaussian.VinogradovDifferenceEnergy
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def residueMixedMoment {κ d : Type*} [Fintype κ] [Fintype d]
    (m s P q : ℕ) (hq : 0 < q) (v : ℕ → d → ℤ) (u : κ → d → ℤ) : ℝ :=
  ∫ theta : UnitAddTorus d,
    residueEnergy P q hq v theta ^ m * ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)

theorem residueMixedMoment_eq_diagonal {κ d : Type*} [Fintype κ] [Fintype d]
    (m s P q : ℕ) (hq : 0 < q) (hPq : P < q)
    (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    residueMixedMoment m s P q hq v u = (P : ℝ) ^ m * moment s u := by
  have : IsEmpty (Fin (P / q)) := by rw [Nat.div_eq_of_lt hPq]; infer_instance
  have he (theta : UnitAddTorus d) : residueEnergy P q hq v theta = (P : ℝ) := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero] using
      residueEnergy_eq_differences P q hq v theta
  unfold residueMixedMoment
  simp_rw [he]
  rw [integral_const_mul]
  simp only [polynomial, one_mul, moment]

end
end RiemannGaussian.VinogradovMixedDifferencing
