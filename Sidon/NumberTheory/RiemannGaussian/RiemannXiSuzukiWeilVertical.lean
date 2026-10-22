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
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Sidon.NumberTheory.RiemannGaussian.GaussianXiLogDerivativeGrowth
import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticCounting
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

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
