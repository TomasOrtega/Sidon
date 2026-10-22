/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer

namespace RiemannGaussian.ZetaStripDisc
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open RiemannGaussian.ZetaGaussianLocalizer
open scoped Topology

theorem analyticAt_regularized {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ regularized s :=
  (differentiable_riemannZeta₁.analyticAt s).div (analyticAt_id.add analyticAt_const)
    (add_one_ne_zero hs.le)

end
end RiemannGaussian.ZetaStripDisc
