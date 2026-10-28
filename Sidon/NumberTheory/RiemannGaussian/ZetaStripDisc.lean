module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer

@[expose] public section

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
