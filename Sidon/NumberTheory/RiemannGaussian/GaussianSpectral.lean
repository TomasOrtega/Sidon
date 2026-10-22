/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace RiemannGaussian

noncomputable section

open Filter Topology
def zetaSpectralCoordinate (s : ℂ) : ℂ :=
  -Complex.I * (s - (1 / 2 : ℝ))

@[simp]
theorem zetaSpectralCoordinate_re (s : ℂ) :
    (zetaSpectralCoordinate s).re = s.im := by
  simp [zetaSpectralCoordinate, Complex.mul_re]

end

end RiemannGaussian
