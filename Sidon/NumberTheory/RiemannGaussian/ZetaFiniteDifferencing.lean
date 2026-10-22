/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Sidon.NumberTheory.RiemannGaussian.LogarithmicShiftPhase
import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

namespace RiemannGaussian.ZetaFiniteDifferencing
noncomputable section
open Complex RiemannGaussian.LogarithmicShiftPhase
open scoped Classical

theorem feature_polar (s : ℂ) (n : ℕ) :
    zetaPrimeFeature s n = (zetaPrimeExpWeight s.re n : ℂ) *
      Complex.exp (((phase s.im (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [zetaPrimeFeature, zetaPrimeExpWeight, phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

end
end RiemannGaussian.ZetaFiniteDifferencing
