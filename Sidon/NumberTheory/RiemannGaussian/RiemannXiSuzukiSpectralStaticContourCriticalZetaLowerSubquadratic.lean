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
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiLogDerivativeGrowth
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

@[expose] public section

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexOrder Topology

namespace RiemannGaussian

noncomputable section

lemma norm_riemannXiCanonicalResidual_le_of_threeHalves_growth
    {A : ℝ} (_hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ ≤
      Real.exp
        (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (riemannXiCanonicalResidual_decomp n).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_riemannXiCanonicalResidual_eq_on_sphere n hw]
    have hxi := hbound w
    have hwnorm : ‖w‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hw
    simpa [R, hwnorm] using hxi
  · rwa [closure_ball 0 hR.ne']

lemma riemannXiCanonicalLog_re_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    (riemannXiCanonicalLog n z).re ≤
      A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  have hid := congrArg norm (exp_riemannXiCanonicalLog_mul_zero_eq n hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hgBound : ‖g z‖ ≤
      Real.exp (A * (R + 1) ^ (3 / 2 : ℝ)) := by
    apply norm_riemannXiCanonicalResidual_le_of_threeHalves_growth hA hbound n
    exact ball_subset_closedBall (by simpa [R] using hz)
  apply Real.exp_le_exp.mp
  calc
    Real.exp (L z).re = Real.exp (L z).re * 1 := by ring
    _ ≤ Real.exp (L z).re * ‖g 0‖ :=
      mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
    _ = ‖g z‖ := hid
    _ ≤ Real.exp (A * (R + 1) ^ (3 / 2 : ℝ)) := hgBound

lemma norm_riemannXiCanonicalLog_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalLog n z‖ ≤
      2 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) * ‖z‖ /
        (xiCanonicalRadius n - ‖z‖) := by
  let R := xiCanonicalRadius n
  let L := riemannXiCanonicalLog n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero
    (M := A * (R + 1) ^ (3 / 2 : ℝ))
    (by positivity) hdiff
  · intro w hw
    exact riemannXiCanonicalLog_re_le_of_threeHalves_growth hA hbound n
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact riemannXiCanonicalLog_zero n

end

end RiemannGaussian
