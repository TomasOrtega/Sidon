/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
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
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
