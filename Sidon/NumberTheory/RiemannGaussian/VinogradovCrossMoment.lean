module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovCrossMoment
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate Classical
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovPartitionEnergy
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def crossGram {ι κ d : Type*} [Fintype ι] [Fintype κ] (v : ι → d → ℤ) (u : κ → d → ℤ)
    (w : ι → ℂ) (z : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, if v i = u j then w i * conj (z j) else 0

theorem crossGram_eq_integral {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (u : κ → d → ℤ) (w : ι → ℂ) (z : κ → ℂ) :
    crossGram v u w z = ∫ theta : UnitAddTorus d,
      polynomial v w theta * conj (polynomial u z theta) := by
  have hi (i : ι) (j : κ) : Integrable (fun theta : UnitAddTorus d =>
      (w i * conj (z j)) * (mFourier (v i) theta * conj (mFourier (u j) theta))) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (theta : UnitAddTorus d) : polynomial v w theta * conj (polynomial u z theta) =
      ∑ i, ∑ j, (w i * conj (z j)) * (mFourier (v i) theta * conj (mFourier (u j) theta)) := by
    simp only [polynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  unfold crossGram
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [integral_const_mul, VinogradovMeanValue.integral_pair]
  split_ifs <;> simp

def crossCount {ι κ d : Type*} [Fintype ι] [Fintype κ] (v : ι → d → ℤ) (u : κ → d → ℤ) : ℕ :=
  (Finset.univ.filter (fun ij : ι × κ => v ij.1 = u ij.2)).card

theorem crossGram_one {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (u : κ → d → ℤ) :
    crossGram v u (fun _ => 1) (fun _ => 1) = (crossCount v u : ℂ) := by
  rw [crossCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  unfold crossGram
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

theorem even_moment_eq_crossGram {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ) :
    ((∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ (2 * s) : ℝ) : ℂ) =
      crossGram (VinogradovShiftedMoment.tupleFrequency s v)
        (VinogradovShiftedMoment.tupleFrequency s v)
        (VinogradovShiftedMoment.tupleWeight s w) (VinogradovShiftedMoment.tupleWeight s w) := by
  have he := VinogradovShiftedMoment.weighted_moment_coefficient s v w 0
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    integral_complex_ofReal, crossGram, VinogradovShiftedMoment.weightedShift, add_zero, polynomial] at he ⊢
  convert he using 1
  congr!

end
end RiemannGaussian.VinogradovCrossMoment
