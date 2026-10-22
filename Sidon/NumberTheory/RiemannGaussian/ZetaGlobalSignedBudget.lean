/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Probability.Moments.ComplexMGF
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

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
