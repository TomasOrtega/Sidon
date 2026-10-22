/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace RiemannGaussian.LogarithmicShiftPhase
noncomputable section

def phase (t x : ℝ) : ℝ := -t * Real.log x

theorem hasDerivAt_phase (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (phase t) (-t / x) x := by
  unfold phase
  convert! (Real.hasDerivAt_log hx.ne').const_mul (-t) using 1

end
end RiemannGaussian.LogarithmicShiftPhase
