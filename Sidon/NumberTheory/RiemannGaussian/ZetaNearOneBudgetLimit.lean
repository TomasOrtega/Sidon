/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

namespace RiemannGaussian.ZetaNearOneBudgetLimit
noncomputable section
open Filter RiemannGaussian.ZetaNearOneLogProfile
open RiemannGaussian.DerivativeOrderComparison RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativePowerExponents
open scoped Topology

def scale (t : ℝ) : ℝ := Real.log (height t)

theorem scale_pos (t : ℝ) : 0 < scale t :=
  Real.log_pos (by linarith [two_le_height t])

theorem scale_atTop : Tendsto scale atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_atTop_mono (fun t : ℝ ↦ show t ≤ |t| + 2 by linarith [le_abs_self t]) tendsto_id)

theorem scale_double_div :
    Tendsto (fun t : ℝ ↦ scale (2 * t) / scale t) atTop (𝓝 1) := by
  have hu : Tendsto (fun t : ℝ ↦ 1 + Real.log 2 / scale t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (scale_atTop.const_div_atTop (Real.log 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro t
    apply (one_le_div (scale_pos t)).mpr
    apply Real.log_le_log (by linarith [two_le_height t])
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  · intro t
    have hh : height (2 * t) ≤ 2 * height t := by
      simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hb := Real.log_le_log (by linarith [two_le_height (2 * t)]) hh
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (by linarith [two_le_height t] : 0 < height t))] at hb
    apply (div_le_iff₀ (scale_pos t)).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ (scale_pos t).ne']
    simpa only [scale, add_comm] using hb

end
end RiemannGaussian.ZetaNearOneBudgetLimit
