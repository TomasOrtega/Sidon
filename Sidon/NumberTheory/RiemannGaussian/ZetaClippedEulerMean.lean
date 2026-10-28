module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.ClippedLogNorm
public import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
public import Sidon.NumberTheory.RiemannGaussian.SechVerticalKernel
public import Sidon.NumberTheory.RiemannGaussian.SechVerticalMoments
public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerLogProfile
public import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer
public import Sidon.NumberTheory.RiemannGaussian.ZetaLogarithmicShiftAllowance
public import Sidon.NumberTheory.RiemannGaussian.ZetaStripDisc

@[expose] public section

namespace RiemannGaussian.ZetaClippedEulerMean
noncomputable section
open Complex MeasureTheory
open RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison RiemannGaussian.ZetaGaussianLocalizer
open RiemannGaussian.ZetaLogarithmicShiftAllowance RiemannGaussian.SechVerticalKernel RiemannGaussian.SechVerticalMoments
def value (k : ℕ) (M y : ℝ) : ℝ :=
  ClippedLogNorm.value M (regularized ((line k : ℂ) + I * (y : ℂ)))

theorem value_lower (k : ℕ) (M y : ℝ) : -M ≤ value k M y := ClippedLogNorm.lower _ _

theorem value_le_profile (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (y : ℝ) :
    value k M y ≤ ZetaEulerLogProfile.profile k y := by
  have hs : ((line k : ℂ) + I * (y : ℂ)).re = line k := by simp
  have hi : ((line k : ℂ) + I * (y : ℂ)).im = y := by simp
  have hz := ZetaEulerLogProfile.regularized_le_exp_profile k hk hs
  rw [hi] at hz
  have hf : Real.exp (-M) ≤ Real.exp (ZetaEulerLogProfile.profile k y) :=
    Real.exp_le_exp.mpr (by linarith [ZetaEulerLogProfile.profile_ge_six k y])
  have h := Real.log_le_log
    (lt_of_lt_of_le (Real.exp_pos (-M)) (le_max_right
      ‖regularized ((line k : ℂ) + I * (y : ℂ))‖ (Real.exp (-M)))) (max_le hz hf)
  simpa only [value, ClippedLogNorm.value, Real.log_exp] using h

theorem continuous_value (k : ℕ) (hk : 1 ≤ k) (M : ℝ) : Continuous (value k M) := by
  have hg : Continuous (fun y : ℝ => regularized ((line k : ℂ) + I * (y : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply (ZetaStripDisc.analyticAt_regularized _).continuousAt.comp (by fun_prop)
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith [half_le_line k hk]
  exact (ClippedLogNorm.continuous M).comp hg

theorem abs_value_shift_le (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b u : ℝ) :
    |value k M (t + b * u)| ≤ ZetaEulerLogProfile.profile k t + M + shiftCost k t b * |u| := by
  have hu := (value_le_profile k hk hM (t + b * u)).trans (ZetaEulerLogProfile.profile_shift_le k t b u)
  have hl := value_lower k M (t + b * u)
  have hp := ZetaEulerLogProfile.profile_ge_six k t
  have hb := mul_nonneg (shiftCost_nonneg k t b) (abs_nonneg u)
  rw [abs_le]
  constructor <;> linarith

theorem integrable_value (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b : ℝ) :
    Integrable (fun u : ℝ => density u * value k M (t + b * u)) := by
  have hc := continuous_density.mul ((continuous_value k hk M).comp
    (by fun_prop : Continuous (fun u : ℝ => t + b * u)))
  apply (integrable_affine_density (ZetaEulerLogProfile.profile k t + M) (shiftCost k t b)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with u
  change ‖density u * value k M (t + b * u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg u)]
  exact mul_le_mul_of_nonneg_left (abs_value_shift_le k hk hM t b u) (density_nonneg u)

end
end RiemannGaussian.ZetaClippedEulerMean
