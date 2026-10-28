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
public import Mathlib.Analysis.SumIntegralComparisons
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

namespace RiemannGaussian.ZetaEulerReciprocalAllowance
noncomputable section
open MeasureTheory Set
open scoped LSeries.notation

theorem pseries_mass_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hq : -σ < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici 1) := by
    intro x hx y _ hxy
    change 1 ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ)) 1
    (by simpa only [Nat.cast_one] using ha) (by simpa only [Nat.cast_one] using hi)
    (by intro y hy; simp only [Nat.cast_one, mem_Ioi] at hy
        exact Real.rpow_nonneg (by linarith) _)
  simp only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)] at ht
  simp only [Real.one_rpow, Nat.add_assoc, Nat.reduceAdd] at ht
  have hs := Real.summable_nat_rpow.mpr hq
  rw [← hs.sum_add_tsum_nat_add 2]
  have hzero : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, hzero, Real.one_rpow, zero_add]
  have he : -(1 : ℝ) / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  linarith

theorem moebius_term_bound (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-s.re) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← one_div]
    exact div_le_div_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem inverse_eq_moebius {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = L (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  apply mul_left_cancel₀ hz
  rw [mul_inv_cancel₀ hz, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs]

theorem inverse_zeta_bound {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [inverse_eq_moebius hs]
  have hsum := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term
        (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
      hsum.norm.tsum_le_tsum (moebius_term_bound s)
        (Real.summable_nat_rpow.mpr (by linarith))
    _ ≤ _ := pseries_mass_bound hs

theorem neg_log_norm_zeta_le {s : ℂ} (hs : 1 < s.re) :
    -Real.log ‖riemannZeta s‖ ≤ Real.log (1 + 1 / (s.re - 1)) := by
  have hn : 0 < ‖(riemannZeta s)⁻¹‖ :=
    norm_pos_iff.mpr (inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs))
  have h := Real.log_le_log hn (inverse_zeta_bound hs)
  rwa [norm_inv, Real.log_inv] at h

end
end RiemannGaussian.ZetaEulerReciprocalAllowance
