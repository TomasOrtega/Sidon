module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianKernel
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovGaussianBounds
noncomputable section
open RiemannGaussian.VinogradovGaussianKernel RiemannGaussian.VinogradovGaussianResonance RiemannGaussian.VinogradovShiftedMoment
open scoped BigOperators

theorem kernel_eq_F_int (a x : ℝ) :
    kernel a x = (1 / a ^ (1 / 2 : ℝ)) *
      HurwitzKernelBounds.F_int 0 ((-x : ℝ) : UnitAddCircle) (1 / a) := by
  unfold kernel HurwitzKernelBounds.F_int
  rw [Function.Periodic.lift_coe]
  congr 1
  apply tsum_congr
  intro n
  simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  congr 1
  ring

def tailEnvelope (a x : ℝ) : ℝ :=
  (1 / a ^ (1 / 2 : ℝ)) *
    ((Real.exp (-Real.pi * (Int.fract (-x)) ^ 2 / a) +
      Real.exp (-Real.pi * (1 - Int.fract (-x)) ^ 2 / a)) /
      (1 - Real.exp (-Real.pi / a)))

theorem tail_denominator_pos {a : ℝ} (ha : 0 < a) :
    0 < 1 - Real.exp (-Real.pi / a) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha

theorem tailEnvelope_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < tailEnvelope a x := by
  unfold tailEnvelope
  exact mul_pos (by positivity)
    (div_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)) (tail_denominator_pos ha))

theorem kernel_le_tailEnvelope {a : ℝ} (ha : 0 < a) (x : ℝ) :
    kernel a x ≤ tailEnvelope a x := by
  have ht : 0 < 1 / a := one_div_pos.mpr ha
  have hr : Int.fract (-x) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [kernel_eq_F_int, ← AddCircle.coe_fract (-x),
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 hr ht]
  unfold tailEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h₀ := HurwitzKernelBounds.F_nat_zero_le hr.1 ht
  have h₁ := HurwitzKernelBounds.F_nat_zero_le (sub_nonneg.mpr hr.2) ht
  have h := add_le_add ((le_abs_self _).trans h₀) ((le_abs_self _).trans h₁)
  simpa only [Real.norm_eq_abs, mul_one_div, ← add_div] using h

def integerDistance (x : ℝ) : ℝ :=
  min (Int.fract (-x)) (1 - Int.fract (-x))

theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := by
  exact le_min (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)

theorem tailEnvelope_le_distance {a : ℝ} (ha : 0 < a) (x : ℝ) :
    tailEnvelope a x ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        Real.exp (-Real.pi * (integerDistance x) ^ 2 / a) := by
  have hG {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
      Real.exp (-Real.pi * v ^ 2 / a) ≤ Real.exp (-Real.pi * u ^ 2 / a) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ha.le
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv 2) Real.pi_pos.le
    nlinarith
  have h₀ := hG (integerDistance_nonneg x)
    (min_le_left (Int.fract (-x)) (1 - Int.fract (-x)))
  have h₁ := hG (integerDistance_nonneg x)
    (min_le_right (Int.fract (-x)) (1 - Int.fract (-x)))
  unfold tailEnvelope
  calc
    _ ≤ (1 / a ^ (1 / 2 : ℝ)) *
        ((Real.exp (-Real.pi * (integerDistance x) ^ 2 / a) +
          Real.exp (-Real.pi * (integerDistance x) ^ 2 / a)) /
          (1 - Real.exp (-Real.pi / a))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (add_le_add h₀ h₁) (tail_denominator_pos ha).le)
        (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

def latticeEnvelope {k : ℕ} (a x : Fin k → ℝ) : ℝ :=
  ∏ j, tailEnvelope (a j) (x j)

theorem latticeKernel_le_envelope {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ j, 0 < a j) (x : Fin k → ℝ) :
    latticeKernel a x ≤ latticeEnvelope a x := by
  exact Finset.prod_le_prod₀ (fun j _ => kernel_nonneg (ha j) (x j))
    (fun j _ => kernel_le_tailEnvelope (ha j) (x j))

def resonanceEnvelope {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a γ : Fin k → ℝ) (v : ι → Fin k → ℤ) : ℝ :=
  ∑ h ∈ differenceSupport (tupleFrequency s v), latticeEnvelope a (linearSample γ h)

theorem resonanceEnvelope_nonneg {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (γ : Fin k → ℝ) (v : ι → Fin k → ℤ) :
    0 ≤ resonanceEnvelope s a γ v := by
  exact Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg
    (fun j _ => (tailEnvelope_pos (ha j) _).le))

theorem resonanceSum_le_envelope {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (γ : Fin k → ℝ) (v : ι → Fin k → ℤ) :
    resonanceSum s a γ v ≤ resonanceEnvelope s a γ v := by
  exact Finset.sum_le_sum (fun h _ => latticeKernel_le_envelope ha (linearSample γ h))

end
end RiemannGaussian.VinogradovGaussianBounds
