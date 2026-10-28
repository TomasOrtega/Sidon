module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Probability.Moments.ComplexMGF
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

@[expose] public section

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Topology

def zetaGlobalRegularCorrection (s : ℂ) : ℂ :=
  1 / s - Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2

theorem zeta_global_complex_budget {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s + logDeriv riemannXi s =
      1 / (s - 1) + zetaGlobalRegularCorrection s := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  rw [logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero (by linarith) hs1
    (riemannZeta_ne_zero_of_one_lt_re hs), zetaGlobalRegularCorrection]
  ring

end
end RiemannGaussian
