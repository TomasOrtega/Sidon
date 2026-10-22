/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.MeasureTheory.Integral.CircleAverage
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneJensen

namespace RiemannGaussian.ZetaAngularPrimeBudget
noncomputable section
open Complex Filter RiemannGaussian.ZetaNearOneLocalDisc RiemannGaussian.ZetaNearOneJensen
open RiemannGaussian.ZetaNearOneLogProfile RiemannGaussian.DerivativeOrderComparison
def budget (k : ℕ) (x t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 +
    (8 * allowance k x t + 2 * allowance k x (2 * t)) / (Real.pi * delta k)

end
end RiemannGaussian.ZetaAngularPrimeBudget
