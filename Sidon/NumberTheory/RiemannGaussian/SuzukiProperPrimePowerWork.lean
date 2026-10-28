module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEnvelope

@[expose] public section

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology

theorem chebyshevPsi_sub_theta_le_eighteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 18 * Real.sqrt x := by
  have hroot (n : ℕ) (hn : 2 ≤ n) :
      Chebyshev.psi (x ^ (1 / (n : ℝ))) ≤ 6 * Real.sqrt x := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 1 ≤ x ^ (1 / (n : ℝ)) := Real.one_le_rpow hx (by positivity)
    refine (chebyshevPsi_le_six_mul_self_of_one_le hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hx
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot 2 (by norm_num)
  have h3 := hroot 3 (by norm_num)
  have h5 := hroot 5 (by norm_num)
  simp only [Nat.cast_ofNat, one_div] at h2 h3 h5
  linarith

end
end RiemannGaussian
