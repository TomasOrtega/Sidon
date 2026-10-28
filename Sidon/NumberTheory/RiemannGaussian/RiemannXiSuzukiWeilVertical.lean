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
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiLogDerivativeGrowth
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticCounting
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

@[expose] public section

open Complex Filter MeasureTheory MeromorphicOn Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

theorem sum_divisor_riemannXi_ball_le_threeHalves_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    ((∑ᶠ i, divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤
      A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
        Real.log 2 := by
  have heq :
      (∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i) =
        ∑ᶠ i, divisor riemannXi
          (closedBall 0 (xiCanonicalRadius n)) i := by
    apply finsum_congr
    intro i
    exact divisor_riemannXi_ball_eq_closedBall n i
  rw [heq]
  exact_mod_cast jensen_riemannXi_divisor_le_threeHalves hA
    (xiCanonicalRadius_pos n) hbound

end

end RiemannGaussian
