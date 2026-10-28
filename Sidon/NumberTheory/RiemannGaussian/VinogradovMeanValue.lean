module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace RiemannGaussian.VinogradovMeanValue
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι]

theorem integral_pair (m n : d → ℤ) :
    (∫ θ : UnitAddTorus d, mFourier m θ * conj (mFourier n θ)) =
      if m = n then (1 : ℂ) else 0 := by
  classical
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) n m
  simpa only [ContinuousMap.inner_toLp, eq_comm, mul_comm] using h

theorem weighted_gram (v : ι → d → ℤ) (w : ι → ℂ) :
    (∫ θ : UnitAddTorus d,
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ)) =
      ∑ i, ∑ j, if v i = v j then w i * conj (w j) else 0 := by
  classical
  have hi (i j : ι) : Integrable (fun θ : UnitAddTorus d =>
      (w i * conj (w j)) * (mFourier (v i) θ * conj (mFourier (v j) θ))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  have he : (fun θ : UnitAddTorus d =>
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ)) =
      fun θ => ∑ i, ∑ j,
        (w i * conj (w j)) * (mFourier (v i) θ * conj (mFourier (v j) θ)) := by
    funext θ
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [integral_const_mul, integral_pair]
  split_ifs <;> simp

theorem product_mFourier {κ : Type*} (S : Finset κ) (v : κ → d → ℤ) (θ : UnitAddTorus d) :
    (∏ i ∈ S, mFourier (v i) θ) = mFourier (∑ i ∈ S, v i) θ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mFourier_zero]
  | @insert i S hi ih => simp [hi, ih, mFourier_add]

theorem power_expansion (v : ι → d → ℤ) (s : ℕ) (θ : UnitAddTorus d) :
    (∑ i, mFourier (v i) θ) ^ s =
      ∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact product_mFourier _ _ _

def moment (s : ℕ) (v : ι → d → ℤ) : ℝ :=
  ∫ θ : UnitAddTorus d, ‖∑ i, mFourier (v i) θ‖ ^ (2 * s)

def collisionCount (s : ℕ) (v : ι → d → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : (Fin s → ι) × (Fin s → ι) =>
    (∑ j, v (p.1 j)) = ∑ j, v (p.2 j))).card

theorem moment_eq_collisionCount (s : ℕ) (v : ι → d → ℤ) :
    moment s v = collisionCount s v := by
  classical
  apply Complex.ofReal_injective
  rw [moment, ← integral_complex_ofReal]
  have he (θ : UnitAddTorus d) :
      ((‖∑ i, mFourier (v i) θ‖ ^ (2 * s) : ℝ) : ℂ) =
      (∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ) *
        conj (∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ) := by
    rw [← power_expansion, Complex.mul_conj, ← Complex.sq_norm, norm_pow]
    congr 1
    ring
  simp_rw [he]
  have h := weighted_gram (fun x : Fin s → ι => ∑ j, v (x j)) (fun _ => 1)
  simp only [one_mul, map_one, mul_one] at h
  rw [h, collisionCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> norm_num

def monomialFrequency (k : ℕ) (n : ℕ) : Fin k → ℤ := fun j => (n : ℤ) ^ (j.val + 1)

def meanValue (s k N : ℕ) : ℝ :=
  moment s (fun n : Fin N => monomialFrequency k (n.val + 1))

theorem meanValue_eq_count (s k N : ℕ) :
    meanValue s k N = collisionCount s (fun n : Fin N => monomialFrequency k (n.val + 1)) :=
  moment_eq_collisionCount _ _

theorem mFourier_real_phase (n : d → ℤ) (α : d → ℝ) :
    mFourier n (fun j => (α j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (n j : ℂ) * (α j : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end RiemannGaussian.VinogradovMeanValue
