/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

open Complex
open scoped Classical LSeries.notation

namespace RiemannGaussian

noncomputable section

theorem norm_zetaPrimeFeature_le_one {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖zetaPrimeFeature s n‖ ≤ 1 := by
  rw [norm_zetaPrimeFeature, zetaPrimeExpWeight]
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.log_natCast_nonneg n]

end
end RiemannGaussian
