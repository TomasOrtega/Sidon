/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
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
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.UniformSpace.UniformApproximation
import Sidon.NumberTheory.RiemannGaussian.GaussianCompletedLogDerivative
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

theorem riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s =
      s * (1 - s) * Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hGammaℝ : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hs
  have hzetaCompleted := riemannZeta_def_of_ne_zero hs0
  have hzetaMul : riemannZeta s * Complex.Gammaℝ s =
      completedRiemannZeta s :=
    (eq_div_iff hGammaℝ).mp hzetaCompleted
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, ← hzetaMul]
  ring

theorem logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaℝ : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hs
  have hGammaℝDiff : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hs
  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hlocal : riemannXi =ᶠ[nhds s]
      (fun z : ℂ ↦
        z * (1 - z) * Complex.Gammaℝ z * riemannZeta z) := by
    filter_upwards
      [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
        eventually_ne_nhds hs1] with z hz hzone
    exact riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hz hzone
  rw [(logDeriv_congr_nhds hlocal).self_of_nhds]
  have hlinear :
      logDeriv (fun z : ℂ ↦ z * (1 - z)) s =
        1 / s + 1 / (s - 1) := by
    have hderivSub : deriv (fun z : ℂ ↦ 1 - z) s = -1 :=
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv.trans (by ring)
    rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z)
      (g := fun z : ℂ ↦ 1 - z) s hs0 h1s
      (by fun_prop) (by fun_prop)]
    simp only [logDeriv_apply, deriv_id'', hderivSub]
    field_simp [hs0, hs1]
    ring
  have hcompleted :
      logDeriv
          (fun z : ℂ ↦ z * (1 - z) * Complex.Gammaℝ z) s =
        1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
          Complex.digamma (s / 2) / 2 := by
    rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z * (1 - z))
      (g := Complex.Gammaℝ) s (mul_ne_zero hs0 h1s) hGammaℝ
      ((by fun_prop) :
        DifferentiableAt ℂ (fun z : ℂ ↦ z * (1 - z)) s)
      hGammaℝDiff]
    rw [hlinear, logDeriv_Gammaℝ hs]
    ring
  rw [logDeriv_fun_mul
    (f := fun z : ℂ ↦ z * (1 - z) * Complex.Gammaℝ z)
    (g := riemannZeta) s
    (mul_ne_zero (mul_ne_zero hs0 h1s) hGammaℝ)
    hzeta
    (((by fun_prop) :
      DifferentiableAt ℂ (fun z : ℂ ↦ z * (1 - z)) s).mul
        hGammaℝDiff)
    hzetaDiff]
  rw [hcompleted]

end

end RiemannGaussian
