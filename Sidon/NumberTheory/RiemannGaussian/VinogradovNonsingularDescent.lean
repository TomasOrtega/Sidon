/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovAffineMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialNonsingular
import Sidon.NumberTheory.RiemannGaussian.VinogradovPowerSumRigidity

namespace RiemannGaussian.VinogradovNonsingularDescent
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovPolynomialSystems RiemannGaussian.VinogradovPolynomialDifferencing
open RiemannGaussian.VinogradovPolynomialNonsingular RiemannGaussian.VinogradovMixedMoments
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem moment_reindex {ι a b : Type*} [Fintype ι] [Fintype a] [Fintype b]
    (s : ℕ) (v : ι → a → ℤ) (e : b ≃ a) :
    moment s (fun x j => v x (e j)) = moment s v := by
  rw [moment_eq_collisionCount, moment_eq_collisionCount]
  congr 1
  unfold collisionCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Finset.sum_apply]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact h i
  · intro h i
    exact h (e i)

theorem monomialTail_moment (s m d p q Q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    moment s (monomialTail m d p q Q) = meanValue s (d + m) Q := by
  let v (x : Fin Q) := VinogradovPowerSumRigidity.integerFrequency (d + m)
    (((p * q : ℕ) : ℤ) * ((x.val + 1 : ℕ) : ℤ))
  have he : monomialTail m d p q Q =
      fun x j => v x (finSumFinEquiv j) := by
    funext x j
    rcases j with j | j
    · simp only [monomialTail, Sum.elim_inl, v, VinogradovPowerSumRigidity.integerFrequency,
        finSumFinEquiv_apply_left, Fin.val_castAdd, Nat.cast_add, Nat.cast_one]
    · simp only [monomialTail, Sum.elim_inr, v, VinogradovPowerSumRigidity.integerFrequency,
        finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.cast_add, Nat.cast_one]
  rw [he, moment_reindex]
  have hscale : ((p * q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hp hq).ne'
  have ha := VinogradovAffineMoment.moment_affine s (d + m)
    (fun x : Fin Q => ((x.val + 1 : ℕ) : ℤ)) hscale 0
  unfold v meanValue monomialFrequency VinogradovPowerSumRigidity.integerFrequency
  unfold VinogradovPowerSumRigidity.integerFrequency at ha
  simpa only [add_zero] using ha

end
end RiemannGaussian.VinogradovNonsingularDescent
