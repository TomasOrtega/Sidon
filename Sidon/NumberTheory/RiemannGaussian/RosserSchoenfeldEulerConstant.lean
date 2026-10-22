/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

open Filter Topology
namespace RiemannGaussian.RosserSchoenfeldEulerConstant
noncomputable section
def massConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - 2 * Real.log 2 - Real.log Real.pi

end
end RiemannGaussian.RosserSchoenfeldEulerConstant
