module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.SechVerticalKernel

@[expose] public section

namespace RiemannGaussian.SechVerticalMoments
noncomputable section
open MeasureTheory Set Filter Real RiemannGaussian.SechVerticalKernel
open scoped Topology

theorem integrable_density : Integrable density := by
  apply integrable_exp_abs.mono' continuous_density.aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg u)]
  exact density_le_exp u

theorem integrable_abs_mul_density : Integrable (fun u : ℝ => |u| * density u) := by
  apply integrable_abs_mul_exp.mono'
    (continuous_abs.mul continuous_density).aestronglyMeasurable
  filter_upwards [] with u
  change ‖|u| * density u‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (density_nonneg _))]
  exact mul_le_mul_of_nonneg_left (density_le_exp u) (abs_nonneg u)

theorem integrable_affine_density (A B : ℝ) :
    Integrable (fun u : ℝ => density u * (A + B * |u|)) := by
  have h := (integrable_density.const_mul A).add (integrable_abs_mul_density.const_mul B)
  convert! h using 1
  ext u
  simp only [Pi.add_apply]
  ring

end
end RiemannGaussian.SechVerticalMoments
