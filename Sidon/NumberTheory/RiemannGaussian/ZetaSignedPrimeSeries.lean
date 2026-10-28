module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

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
