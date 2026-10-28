module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResidueEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSignedCongruence

@[expose] public section

namespace RiemannGaussian.VinogradovProductEnergy
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovResidueEnergy RiemannGaussian.VinogradovMomentPartition RiemannGaussian.VinogradovPartitionEnergy
theorem polynomial_prod {α β d : Type*} [Fintype α] [Fintype β] [Fintype d]
    (v : α → d → ℤ) (u : β → d → ℤ) (w : α → ℂ) (z : β → ℂ)
    (theta : UnitAddTorus d) :
    polynomial (fun x : α × β => v x.1 + u x.2) (fun x => w x.1 * z x.2) theta =
      polynomial v w theta * polynomial u z theta := by
  unfold polynomial
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [mFourier_add]
  ring

def blockFrequency {p k a xi X : ℕ} (colour : Fin k → Bool)
    (x : ConditionedWindow p k a xi X) : Fin k → ℤ :=
  fun i => ∑ j, VinogradovSignedCongruence.sign (colour j) * ((x.val j).val + 1 : ℤ) ^ (i.val + 1)

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end
end RiemannGaussian.VinogradovProductEnergy
