/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.UniformSpace.UniformApproximation
import Sidon.NumberTheory.RiemannGaussian.VinogradovDiagonalExponent
import Sidon.NumberTheory.RiemannGaussian.VinogradovDiagonalIteration

namespace RiemannGaussian.VinogradovExponentialDefect
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovDiagonalIteration
theorem defect_le_exp {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    defect k n ≤ ((k : ℝ) ^ 2 / 2) * Real.exp (-(n : ℝ) / k) := by
  have hfactor : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (k : ℝ)))]
  have hp := pow_le_pow_left₀ (factor_nonneg hk) hfactor n
  rw [← Real.exp_nat_mul] at hp
  have he : (n : ℝ) * (-(1 / (k : ℝ))) = -(n : ℝ) / k := by ring
  rw [he] at hp
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h := VinogradovDiagonalExponent.power_gap hk 0 (0 : ℝ)
    rw [← Nat.choose_two_right] at h
    norm_num [VinogradovDiagonalExponent.exponent, VinogradovDiagonalExponent.degreeWeight] at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_le_mul hc hp (pow_nonneg (factor_nonneg hk) n)
    (by positivity : 0 ≤ (k : ℝ) ^ 2 / 2)

theorem exp_neg_three_le : Real.exp (-3 : ℝ) ≤ 1 / 20 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20)
    (show 20 ≤ Real.exp 3 by linarith)

theorem exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 50 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 50)
    (show 50 ≤ Real.exp 4 by linarith)

theorem defect_three_degree_le {k : ℕ} (hk : 1 ≤ k) :
    defect k (3 * k) ≤ (k : ℝ) ^ 2 / 40 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := defect_le_exp hk (3 * k)
  have he : -((3 * k : ℕ) : ℝ) / k = -3 := by push_cast; field_simp
  rw [he] at h
  calc
    _ ≤ (k : ℝ) ^ 2 / 2 * Real.exp (-3) := h
    _ ≤ (k : ℝ) ^ 2 / 2 * (1 / 20) :=
      mul_le_mul_of_nonneg_left exp_neg_three_le (by positivity)
    _ = _ := by ring

theorem defect_four_degree_le {k : ℕ} (hk : 1 ≤ k) :
    defect k (4 * k) ≤ (k : ℝ) ^ 2 / 100 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := defect_le_exp hk (4 * k)
  have he : -((4 * k : ℕ) : ℝ) / k = -4 := by push_cast; field_simp
  rw [he] at h
  calc
    _ ≤ (k : ℝ) ^ 2 / 2 * Real.exp (-4) := h
    _ ≤ (k : ℝ) ^ 2 / 2 * (1 / 50) :=
      mul_le_mul_of_nonneg_left exp_neg_four_le (by positivity)
    _ = _ := by ring

end
end RiemannGaussian.VinogradovExponentialDefect
