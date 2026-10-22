/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEnvelope

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
