module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovProductEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovMixedMoments
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovPartitionEnergy RiemannGaussian.VinogradovProductEnergy
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mixedMoment {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : ℝ :=
  ∫ theta : UnitAddTorus d,
    ‖polynomial v (fun _ => 1) theta‖ ^ (2 * r) *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)

def configurationFrequency {ι κ d : Type*} (r s : ℕ)
    (v : ι → d → ℤ) (u : κ → d → ℤ)
    (x : (Fin r → ι) × (Fin s → κ)) : d → ℤ :=
  tupleFrequency r v x.1 + tupleFrequency s u x.2

theorem tuple_polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (a : ι → ℂ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency r v) (tupleWeight r a) theta =
      polynomial v a theta ^ r := (weighted_power_expansion r v a theta).symm

theorem configuration_polynomial {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) (a : ι → ℂ) (b : κ → ℂ)
    (theta : UnitAddTorus d) :
    polynomial (configurationFrequency r s v u)
      (fun x => tupleWeight r a x.1 * tupleWeight s b x.2) theta =
      polynomial v a theta ^ r * polynomial u b theta ^ s := by
  change polynomial (fun x : (Fin r → ι) × (Fin s → κ) =>
    tupleFrequency r v x.1 + tupleFrequency s u x.2) _ theta = _
  rw [polynomial_prod, tuple_polynomial, tuple_polynomial]

theorem mixedMoment_eq_energy {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    mixedMoment r s v u = ∫ theta : UnitAddTorus d,
      ‖polynomial (configurationFrequency r s v u) (fun _ => 1) theta‖ ^ 2 := by
  unfold mixedMoment
  apply integral_congr_ae
  filter_upwards [] with theta
  have h := configuration_polynomial r s v u (fun _ => 1) (fun _ => 1) theta
  simp only [tupleWeight, Finset.prod_const_one, one_mul] at h
  rw [h, norm_mul, norm_pow, norm_pow, mul_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm r 2, Nat.mul_comm s 2]

theorem mixedMoment_eq_count {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    mixedMoment r s v u = differenceCount (configurationFrequency r s v u) 0 := by
  rw [mixedMoment_eq_energy]
  have h := weightedShift_one (configurationFrequency r s v u) 0
  rw [weightedShift_zero] at h
  simpa only [polynomial, one_mul, Complex.ofReal_re, Complex.natCast_re] using
    congrArg Complex.re h

theorem mixedMoment_nonneg {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : 0 ≤ mixedMoment r s v u :=
  integral_nonneg (fun _ => by positivity)

end
end RiemannGaussian.VinogradovMixedMoments
