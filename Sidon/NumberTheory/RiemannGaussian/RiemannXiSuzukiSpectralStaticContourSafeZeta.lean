module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
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
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
open scoped ArithmeticFunction.Moebius Classical ComplexConjugate ENNReal
  Interval LSeries.notation Topology

namespace RiemannGaussian

noncomputable section

def staticContourSafeZetaDirichletMass : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

theorem summable_staticContourSafeZetaDirichletSeries :
    Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  exact Real.summable_nat_rpow_inv.mpr (by norm_num)

theorem one_le_staticContourSafeZetaDirichletMass :
    1 ≤ staticContourSafeZetaDirichletMass := by
  unfold staticContourSafeZetaDirichletMass
  have hone : (((1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ = 1 := by norm_num
  rw [← hone]
  apply summable_staticContourSafeZetaDirichletSeries.le_tsum 1
  intro n _hn
  positivity

theorem norm_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖riemannZeta s‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum := summable_riemannZetaSummand hsOne
  rw [← tsum_riemannZetaSummand hsOne]
  calc
    ‖∑' n : ℕ, riemannZetaSummandHom
        (Complex.ne_zero_of_one_lt_re hsOne) n‖ ≤
        ∑' n : ℕ, ‖riemannZetaSummandHom
          (Complex.ne_zero_of_one_lt_re hsOne) n‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = staticContourSafeZetaDirichletMass := by
      unfold staticContourSafeZetaDirichletMass
      apply tsum_congr
      intro n
      simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk,
        ZeroHom.coe_mk]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
          (by rw [neg_re, hs]; norm_num),
        neg_re, hs, Real.rpow_neg (Nat.cast_nonneg n)]

theorem norm_moebius_LSeries_term_safeLine_le
    {s : ℂ} (hs : s.re = 3 / 2) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦
        ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos hnpos, hs]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_moebius_LSeries_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖L (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
      staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum : LSeriesSummable
      (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsOne
  calc
    ‖L (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
        ∑' n : ℕ, ‖LSeries.term
          (fun m : ℕ ↦ ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      hsum.norm.tsum_le_tsum
        (norm_moebius_LSeries_term_safeLine_le hs)
        summable_staticContourSafeZetaDirichletSeries
    _ = staticContourSafeZetaDirichletMass := rfl

theorem norm_inv_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖(riemannZeta s)⁻¹‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsOne
  have hmul : riemannZeta s *
      L (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsOne]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hsOne
  have hinv : (riemannZeta s)⁻¹ =
      L (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
    apply mul_left_cancel₀ hzeta
    rw [mul_inv_cancel₀ hzeta, hmul]
  rw [hinv]
  exact norm_moebius_LSeries_safeLine_le_mass hs

end

end RiemannGaussian
