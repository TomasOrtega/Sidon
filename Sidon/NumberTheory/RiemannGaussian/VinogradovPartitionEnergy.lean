/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCongruenceEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentPartition
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovPartitionEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMomentPartition
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (theta : UnitAddTorus d) : ℂ :=
  ∑ i, w i * mFourier (v i) theta

theorem continuous_polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) : Continuous (polynomial v w) := by
  unfold polynomial
  fun_prop

theorem integrable_polynomial_energy {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) :
    Integrable (fun theta : UnitAddTorus d => ‖polynomial v w theta‖ ^ 2) :=
  ((continuous_polynomial v w).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem polynomial_target_refinement {ι κ ν d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (fine : ι → κ) (coarse : κ → ν)
    (target : ν) (theta : UnitAddTorus d) :
    polynomial v (targetWeight (coarse ∘ fine) w target) theta =
      ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
        polynomial v (targetWeight fine w c) theta := by
  unfold polynomial
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : coarse (fine i) = target
  · rw [Finset.sum_eq_single (fine i)]
    · simp [targetWeight, hs]
    · intro c hc hne
      simp [targetWeight, Ne.symm hne]
    · intro hn
      exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩))
  · have hz : ∀ c ∈ Finset.univ.filter (fun c => coarse c = target), fine i ≠ c := by
      intro c hc he
      apply hs
      rw [he]
      exact (Finset.mem_filter.mp hc).2
    rw [Finset.sum_eq_zero (fun c hc => by simp [targetWeight, hz c hc])]
    simp [targetWeight, hs]

theorem target_energy_le {ι κ ν d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (fine : ι → κ) (coarse : κ → ν)
    (target : ν) (D : ℝ)
    (hcard : ((Finset.univ.filter (fun c => coarse c = target)).card : ℝ) ≤ D)
    (theta : UnitAddTorus d) :
    ‖polynomial v (targetWeight (coarse ∘ fine) w target) theta‖ ^ 2 ≤
      D * ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
        ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
  rw [polynomial_target_refinement v w fine coarse target theta]
  exact (VinogradovCongruenceEnergy.sum_energy_le_card_mul _ _).trans
    (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem target_integral_le {ι κ ν d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (fine : ι → κ) (coarse : κ → ν)
    (target : ν) (D : ℝ)
    (hcard : ((Finset.univ.filter (fun c => coarse c = target)).card : ℝ) ≤ D) :
    (∫ theta : UnitAddTorus d,
      ‖polynomial v (targetWeight (coarse ∘ fine) w target) theta‖ ^ 2) ≤
      D * ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
        ∫ theta : UnitAddTorus d, ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
  have hi (c : κ) := integrable_polynomial_energy v (targetWeight fine w c)
  calc
    (∫ theta : UnitAddTorus d,
        ‖polynomial v (targetWeight (coarse ∘ fine) w target) theta‖ ^ 2) ≤
        ∫ theta : UnitAddTorus d,
          D * ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
            ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
      apply integral_mono (integrable_polynomial_energy _ _)
        ((integrable_finsetSum _ (fun c _ => hi c)).const_mul D)
      exact target_energy_le v w fine coarse target D hcard
    _ = D * ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
        ∫ theta : UnitAddTorus d, ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun c _ => hi c)]

theorem whole_integral_le {ι κ ν d : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (fine : ι → κ) (coarse : κ → ν) (D : ℝ)
    (hcollision : ∀ i j, v i = v j → coarse (fine i) = coarse (fine j))
    (hcard : ∀ target, ((Finset.univ.filter (fun c => coarse c = target)).card : ℝ) ≤ D) :
    (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) ≤
      D * ∑ c : κ, ∫ theta : UnitAddTorus d, ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
  have hg := weightedShift_partition v w (coarse ∘ fine) hcollision
  simp only [VinogradovShiftedMoment.weightedShift_zero] at hg
  have hr := congrArg Complex.re hg
  simp only [Complex.re_sum, Complex.ofReal_re] at hr
  change (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) =
    ∑ target : ν, ∫ theta : UnitAddTorus d,
      ‖polynomial v (targetWeight (coarse ∘ fine) w target) theta‖ ^ 2 at hr
  rw [hr]
  calc
    (∑ target : ν, ∫ theta : UnitAddTorus d,
        ‖polynomial v (targetWeight (coarse ∘ fine) w target) theta‖ ^ 2) ≤
        ∑ target : ν, D * ∑ c ∈ Finset.univ.filter (fun c => coarse c = target),
          ∫ theta : UnitAddTorus d, ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 :=
      Finset.sum_le_sum (fun target _ => target_integral_le v w fine coarse target D (hcard target))
    _ = D * ∑ c : κ, ∫ theta : UnitAddTorus d,
        ‖polynomial v (targetWeight fine w c) theta‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

end
end RiemannGaussian.VinogradovPartitionEnergy
