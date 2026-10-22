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
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.UniformSpace.UniformApproximation

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology LSeries.notation ArithmeticFunction

namespace RiemannGaussian

noncomputable section

theorem vonMangoldt_LSeries_term_eq_phase (a y : ℝ) (n : ℕ) :
    LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * y) n =
      ((ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) : ℝ) : ℂ) *
        Complex.exp (-(I * ((y * Real.log n : ℝ) : ℂ))) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log,
      ← Complex.exp_neg]
    have he : -((Real.log (n : ℝ) : ℂ) * ((a : ℂ) + I * y)) =
        ((-a * Real.log (n : ℝ) : ℝ) : ℂ) + -(I * ((y * Real.log (n : ℝ) : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [he, Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring

theorem vonMangoldt_LSeries_term_re (a y : ℝ) (n : ℕ) :
    (LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * y) n).re =
      ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) * Real.cos (y * Real.log n) := by
  rw [vonMangoldt_LSeries_term_eq_phase]
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp only [neg_re, neg_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, neg_zero, Real.exp_zero, Real.cos_neg]

theorem neg_logDeriv_riemannZeta_eq_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s =
      ∑' n, LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s n := by
  simpa only [logDeriv_apply, neg_div, LSeries] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

theorem neg_logDeriv_riemannZeta_three_height_nonneg {a : ℝ} (ha : 1 < a) (y : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta (a : ℂ)).re +
      4 * (-logDeriv riemannZeta ((a : ℂ) + I * y)).re +
      (-logDeriv riemannZeta ((a : ℂ) + I * ((2 * y : ℝ) : ℂ))).re := by
  let f : ℝ → ℕ → ℂ := fun t ↦ LSeries.term
    (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * t)
  have hs (t : ℝ) : Summable (f t) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using ha)
  have hsre (t : ℝ) : Summable (fun n ↦ (f t n).re) := Complex.reCLM.summable (hs t)
  have hre (t : ℝ) : (-logDeriv riemannZeta ((a : ℂ) + I * t)).re = ∑' n, (f t n).re := by
    rw [neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using ha), Complex.re_tsum (hs t)]
  have hreal : (-logDeriv riemannZeta (a : ℂ)).re = ∑' n, (f 0 n).re := by
    simpa using hre 0
  rw [hreal, hre y, hre (2 * y), ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((hsre 0).mul_left 3) ((hsre y).mul_left 4),
    ← Summable.tsum_add (((hsre 0).mul_left 3).add ((hsre y).mul_left 4)) (hsre (2 * y))]
  apply tsum_nonneg
  intro n
  dsimp [f]
  have hzero := vonMangoldt_LSeries_term_re a 0 n
  simp only [ofReal_zero, zero_mul, Real.cos_zero, mul_one] at hzero
  rw [hzero, vonMangoldt_LSeries_term_re a y n,
    vonMangoldt_LSeries_term_re a (2 * y) n]
  simp only [mul_assoc (2 : ℝ), Real.cos_two_mul]
  have hnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  nlinarith [mul_nonneg hnonneg (sq_nonneg (1 + Real.cos (y * Real.log n)))]

end

end RiemannGaussian
