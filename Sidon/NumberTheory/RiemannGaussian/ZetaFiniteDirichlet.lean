module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

@[expose] public section

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
