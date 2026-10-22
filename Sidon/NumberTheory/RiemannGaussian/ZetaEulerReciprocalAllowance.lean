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
import Mathlib.Analysis.SumIntegralComparisons
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
