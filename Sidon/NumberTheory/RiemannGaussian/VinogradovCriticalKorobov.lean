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
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
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
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Sidon.NumberTheory.RiemannGaussian.VinogradovFirstExponent
public import Sidon.NumberTheory.RiemannGaussian.VinogradovInitialExceptional
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

@[expose] public section

namespace RiemannGaussian.VinogradovCriticalKorobov
noncomputable section
open scoped Classical BigOperators
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
theorem moment_le_of_frequency_embedding {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (w : κ → d → ℤ) (e : ι ↪ κ) (he : ∀ i, w (e i) = v i) :
    moment r v ≤ moment r w := by
  simp only [VinogradovInitialExceptional.moment_eq_crossCount]
  apply Nat.cast_le.mpr
  let E : (Fin r → ι) ↪ (Fin r → κ) := ⟨fun x j => e (x j), by
    intro x y h
    funext j
    exact e.injective (congrArg (fun z => z j) h)⟩
  apply VinogradovFirstExponent.crossCount_le_of_embedding _ _ E
  intro x
  funext j
  simp only [tupleFrequency, Finset.sum_apply]
  change (∑ l : Fin r, w (e (x l)) j) = ∑ l : Fin r, v (x l) j
  simp only [he]

theorem finite_moment_le_interval (r k Y : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ Y) :
    moment r (fun b : B => monomialFrequency k b.val) ≤ meanValue r k Y := by
  let e : B ↪ Fin Y := ⟨fun b => ⟨b.val - 1, by have h := hB b.val b.property; omega⟩, by
    intro b c h
    have hv := congrArg Fin.val h
    have hb := (hB b.val b.property).1
    have hc := (hB c.val c.property).1
    apply Subtype.ext
    dsimp only at hv
    omega⟩
  apply moment_le_of_frequency_embedding r _ _ e
  intro b
  change monomialFrequency k (b.val - 1 + 1) = monomialFrequency k b.val
  rw [Nat.sub_add_cancel (hB b.val b.property).1]

end
end RiemannGaussian.VinogradovCriticalKorobov
