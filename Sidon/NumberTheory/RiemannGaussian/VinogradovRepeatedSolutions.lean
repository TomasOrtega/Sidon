/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovProductEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovRepeatedSolutions
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open UnitAddTorus MeasureTheory RiemannGaussian.VinogradovPartitionEnergy RiemannGaussian.VinogradovMeanValue
open RiemannGaussian.VinogradovShiftedMoment RiemannGaussian.VinogradovProductEnergy
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def repeatedFrequency {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (z : ι × (Fin s → ι)) : d → ℤ :=
  (fun j => 2 * v z.1 j) + tupleFrequency s v z.2

theorem tuple_polynomial_one {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency s v) (fun _ => 1) theta = polynomial v (fun _ => 1) theta ^ s := by
  symm
  simpa only [tupleWeight, Finset.prod_const_one, polynomial] using weighted_power_expansion s v (fun _ => 1) theta

theorem repeated_polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (repeatedFrequency s v) (fun _ => 1) theta =
      polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1) theta *
        polynomial v (fun _ => 1) theta ^ s := by
  unfold repeatedFrequency
  have hp := polynomial_prod (fun i j => (2 : ℤ) * v i j) (tupleFrequency s v)
    (fun _ => 1) (fun _ => 1) theta
  simpa only [one_mul, tuple_polynomial_one] using hp

theorem tupleFrequency_eq_repeated {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (x : Fin (s + 2) → ι) (hx : x 0 = x 1) :
    tupleFrequency (s + 2) v x = repeatedFrequency s v (x 0, fun j => x j.succ.succ) := by
  funext j
  simp only [tupleFrequency, repeatedFrequency, Pi.add_apply, Finset.sum_apply, Fin.sum_univ_succ]
  change x 0 = x (0 : Fin (s + 1)).succ at hx
  rw [← hx]
  ring

end
end RiemannGaussian.VinogradovRepeatedSolutions

namespace RiemannGaussian.VinogradovRepeatedSolutions.Pairs
noncomputable section
open scoped Classical BigOperators
open RiemannGaussian.VinogradovShiftedMoment RiemannGaussian.VinogradovRepeatedSolutions RiemannGaussian.VinogradovPartitionEnergy RiemannGaussian.VinogradovMeanValue
theorem exists_pair_permutation {α : Type*} (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm α, e a = c ∧ e b = d := by
  have hf : Function.Injective (fun z : Bool => if z then b else a) := by
    intro x y h
    cases x <;> cases y <;> simp_all
  have hg : Function.Injective (fun z : Bool => if z then d else c) := by
    intro x y h
    cases x <;> cases y <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  exact ⟨e, by simpa using he false, by simpa using he true⟩

theorem tupleFrequency_comp_perm {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (x : Fin s → ι) (e : Equiv.Perm (Fin s)) :
    tupleFrequency s v (x ∘ e) = tupleFrequency s v x := by
  funext j
  simpa only [tupleFrequency, Finset.sum_apply, Function.comp_apply] using
    Equiv.sum_comp e (fun i => v (x i) j)

end
end RiemannGaussian.VinogradovRepeatedSolutions.Pairs
