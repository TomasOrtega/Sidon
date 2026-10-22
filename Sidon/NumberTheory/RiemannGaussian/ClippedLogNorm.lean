/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace RiemannGaussian.ClippedLogNorm
noncomputable section

def value (M : ℝ) (z : ℂ) : ℝ := Real.log (max ‖z‖ (Real.exp (-M)))

theorem continuous (M : ℝ) : Continuous (value M) := by
  apply (continuous_norm.max continuous_const).log
  intro z
  exact (lt_of_lt_of_le (Real.exp_pos _) (le_max_right ‖z‖ _)).ne'

theorem lower (M : ℝ) (z : ℂ) : -M ≤ value M z := by
  simpa only [Real.log_exp, value] using
    Real.log_le_log (Real.exp_pos (-M)) (le_max_right ‖z‖ (Real.exp (-M)))

end
end RiemannGaussian.ClippedLogNorm
