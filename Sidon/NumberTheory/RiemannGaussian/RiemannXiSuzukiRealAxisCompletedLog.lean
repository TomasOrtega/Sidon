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
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.TaylorSeries
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
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Sidon.NumberTheory.RiemannGaussian.GaussianCompletedLogDerivative
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

@[expose] public section

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
