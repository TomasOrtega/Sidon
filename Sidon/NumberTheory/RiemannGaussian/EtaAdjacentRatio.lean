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
import Mathlib.Analysis.Complex.Convex
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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

namespace RiemannGaussian
noncomputable section
open Complex Set
open scoped Classical

def pairedEtaStepLog (x : ℝ) : ℝ := Real.log ((x + 1) / x)

def pairedEtaAdjacentRatio (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (pairedEtaStepLog x : ℂ))

def pairedEtaAdjacentInverse (s : ℂ) (x : ℝ) : ℂ :=
  (1 + pairedEtaAdjacentRatio s x)⁻¹

theorem pairedEtaStepLog_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ pairedEtaStepLog x ∧ pairedEtaStepLog x ≤ 1 / x := by
  have hr : 1 ≤ (x + 1) / x := (le_div_iff₀ hx).mpr (by linarith)
  constructor
  · exact Real.log_nonneg hr
  · have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hr)
    apply h.trans_eq
    field_simp
    ring

theorem pairedEtaStepLog_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    pairedEtaStepLog y ≤ pairedEtaStepLog x := by
  have hy : 0 < y := hx.trans_le hxy
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (hx.trans_le hxy) hx]
  nlinarith

theorem norm_exp_sub_exp_le_of_re_nonpos {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp w - Complex.exp z‖ ≤ ‖w - z‖ := by
  have h := (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => show ‖Complex.exp u‖ ≤ (1 : ℝ) by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hu) hz hw
  simpa using h

theorem re_pairedEtaAdjacentRatio_nonneg {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 0 ≤ (pairedEtaAdjacentRatio s x).re := by
  have hlog := pairedEtaStepLog_bounds hx
  have hangle : |s.im * pairedEtaStepLog x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlog.1]
    calc
      |s.im| * pairedEtaStepLog x ≤ ‖s‖ * pairedEtaStepLog x :=
        mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) hlog.1
      _ ≤ x * (1 / x) := mul_le_mul hscale hlog.2 hlog.1 (by positivity)
      _ = 1 := by field_simp
  have hcos : 0 ≤ Real.cos (s.im * pairedEtaStepLog x) := by
    apply Real.cos_nonneg_of_mem_Icc
    have hpi := Real.pi_gt_three
    constructor <;> linarith [(abs_le.mp hangle).1, (abs_le.mp hangle).2]
  rw [pairedEtaAdjacentRatio, Complex.exp_re]
  simp only [neg_mul, neg_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, Real.cos_neg]
  exact mul_nonneg (Real.exp_pos _).le hcos

theorem one_le_norm_one_add_pairedEtaAdjacentRatio {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 1 ≤ ‖1 + pairedEtaAdjacentRatio s x‖ := by
  have h := re_pairedEtaAdjacentRatio_nonneg hx hscale
  have hn := Complex.re_le_norm (1 + pairedEtaAdjacentRatio s x)
  simp only [Complex.add_re, Complex.one_re] at hn
  linarith

theorem norm_pairedEtaAdjacentInverse_le_one {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : ‖pairedEtaAdjacentInverse s x‖ ≤ 1 := by
  rw [pairedEtaAdjacentInverse, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale)

theorem norm_pairedEtaAdjacentRatio_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hleft (u : ℝ) (hu : 0 < u) : (-s * (pairedEtaStepLog u : ℂ)).re ≤ 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hs (pairedEtaStepLog_bounds hu).1)
  have h := norm_exp_sub_exp_le_of_re_nonpos (hleft x hx) (hleft y (hx.trans_le hxy))
  unfold pairedEtaAdjacentRatio
  apply h.trans_eq
  rw [show -s * (pairedEtaStepLog y : ℂ) - -s * (pairedEtaStepLog x : ℂ) =
    s * ((pairedEtaStepLog x - pairedEtaStepLog y : ℝ) : ℂ) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (pairedEtaStepLog_antitone hx hxy))]

theorem norm_pairedEtaAdjacentInverse_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hscale : ‖s‖ ≤ x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hx1 := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hy1 := one_le_norm_one_add_pairedEtaAdjacentRatio (hx.trans_le hxy) (hscale.trans hxy)
  have hx0 : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  have hy0 : 1 + pairedEtaAdjacentRatio s y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy1; linarith
  have he : pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x =
      (pairedEtaAdjacentRatio s x - pairedEtaAdjacentRatio s y) /
        ((1 + pairedEtaAdjacentRatio s y) * (1 + pairedEtaAdjacentRatio s x)) := by
    unfold pairedEtaAdjacentInverse
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_sub_rev]
  calc
    _ ≤ ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ :=
      div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hy1 hx1)
    _ ≤ _ := norm_pairedEtaAdjacentRatio_sub_le hs hx hxy

theorem cpow_add_one_eq_pairedEtaAdjacentRatio_mul (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x + 1 : ℝ) : ℂ) ^ (-s) = pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log (by linarith : 0 ≤ x + 1), ← Complex.ofReal_log hx.le,
    pairedEtaAdjacentRatio, ← Complex.exp_add]
  congr 1
  unfold pairedEtaStepLog
  rw [Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
  push_cast
  ring

theorem pairedEtaAdjacentInverse_mul_add (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    pairedEtaAdjacentInverse s x *
        ((x : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) = (x : ℂ) ^ (-s) := by
  rw [cpow_add_one_eq_pairedEtaAdjacentRatio_mul s hx]
  have hn := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hz : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; linarith
  unfold pairedEtaAdjacentInverse
  rw [show (x : ℂ) ^ (-s) + pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) =
    (1 + pairedEtaAdjacentRatio s x) * (x : ℂ) ^ (-s) by ring,
    ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

end
end RiemannGaussian
