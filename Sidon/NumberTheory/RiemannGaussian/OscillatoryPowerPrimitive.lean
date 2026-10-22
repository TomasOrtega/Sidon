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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
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
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Probability.Moments.ComplexMGF
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

namespace RiemannGaussian.OscillatoryPowerPrimitive
noncomputable section
open Complex MeasureTheory Set
open scoped Interval

def mode (r : ℂ) (w x : ℝ) : ℂ := exp (I * w * x) * (x : ℂ) ^ r

def denominator (r : ℂ) (w x : ℝ) : ℂ := I * w * x + r

def primitive (r : ℂ) (w x : ℝ) : ℂ :=
  exp (I * w * x) * (x : ℂ) ^ (r + 1) / denominator r w x

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

theorem hasDerivAt_primitive (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x)
    (hd : denominator r w x ≠ 0) :
    HasDerivAt (primitive r w)
      (mode r w x + r * mode r w x / denominator r w x ^ 2) x := by
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).cexp
  have hp := power_deriv (r + 1) hx
  have hl := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).add_const r
  apply ((he.mul hp).div hl hd).congr_deriv
  dsimp
  rw [show r + 1 - 1 = r by ring]
  rw [cpow_add r 1 (Complex.ofReal_ne_zero.mpr hx.ne'), cpow_one]
  unfold mode denominator
  unfold denominator at hd
  field_simp [hd]
  ring

theorem norm_mode (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mode r w x‖ = x ^ r.re := by
  unfold mode
  rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem denominator_lower (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    |w| * x / 2 ≤ ‖denominator r w x‖ := by
  have hi : (denominator r w x).im = w * x + r.im := by simp [denominator]
  have ht : |w| * x ≤ |w * x + r.im| + |r.im| := by
    have h := abs_add_le (w * x + r.im) (-r.im)
    simpa only [add_neg_cancel_right, abs_neg, abs_mul, abs_of_nonneg hx] using h
  have hn := abs_im_le_norm (denominator r w x)
  rw [hi] at hn
  linarith

theorem denominator_ne_zero (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) : denominator r w x ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by positivity : 0 < |w| * x / 2).trans_le (denominator_lower r w hx.le hsep)

theorem norm_primitive_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖primitive r w x‖ ≤ 2 / |w| * x ^ r.re := by
  have hd := denominator_lower r w hx.le hsep
  have hn : ‖exp (I * w * x) * (x : ℂ) ^ (r + 1)‖ = x ^ (r.re + 1) := by
    simpa only [mode, add_re, one_re] using norm_mode (r + 1) w hx
  unfold primitive
  rw [norm_div, hn]
  apply (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) hd).trans_eq
  rw [Real.rpow_add hx, Real.rpow_one]
  field_simp

theorem norm_defect_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖r * mode r w x / denominator r w x ^ 2‖ ≤
      4 * ‖r‖ / |w| ^ 2 * x ^ (r.re - 2) := by
  have hd := denominator_lower r w hx.le hsep
  rw [norm_div, norm_mul, norm_pow, norm_mode r w hx]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hd 2)).trans_eq
  rw [Real.rpow_sub hx, Real.rpow_two]
  field_simp
  ring

private theorem mode_continuousOn (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (mode r w) [[a, b]] := by
  unfold mode
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

theorem intervalIntegrable_mode (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (mode r w) volume a b :=
  (mode_continuousOn r w ha hab).intervalIntegrable

theorem integral_eq (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    (∫ x : ℝ in a..b, mode r w x) = primitive r w b - primitive r w a -
      ∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2 := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hm : IntervalIntegrable (mode r w) volume a b :=
    (mode_continuousOn r w ha hab).intervalIntegrable
  have hd : IntervalIntegrable (fun x ↦ r * mode r w x / denominator r w x ^ 2)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuousOn_const.mul (mode_continuousOn r w ha hab))
      (by unfold denominator; fun_prop)
    exact fun x hx ↦ pow_ne_zero 2 (denominator_ne_zero r hw (hs hx).1 (hs hx).2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hasDerivAt_primitive r w (hs hx).1
      (denominator_ne_zero r hw (hs hx).1 (hs hx).2)) (hm.add hd)
  rw [intervalIntegral.integral_add hm hd] at h
  exact eq_sub_of_add_eq h

theorem norm_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, mode r w x‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (r.re - 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun x hx ↦ Or.inl (hs hx).1.ne'
  have hd : ‖∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2‖ ≤
      (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro x hx
      exact norm_defect_le r hw (ha.trans hx.1)
        (hsep.trans (mul_le_mul_of_nonneg_left hx.1.le (abs_nonneg w)))
    · exact hi.const_mul _
  rw [integral_eq r hw ha hab hsep]
  have hb := norm_primitive_le r hw (ha.trans_le hab)
    (hsep.trans (mul_le_mul_of_nonneg_left hab (abs_nonneg w)))
  have hna := norm_primitive_le r hw ha hsep
  apply (norm_sub_le _ _).trans
  have he := (norm_sub_le (primitive r w b) (primitive r w a)).trans (add_le_add hb hna)
  exact (add_le_add he hd).trans_eq (by ring)

theorem cosine_eq_modes (r : ℂ) (w x : ℝ) :
    (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r = (mode r w x + mode r (-w) x) / 2 := by
  rw [ofReal_cos, Complex.cos]
  unfold mode
  push_cast
  ring_nf

theorem norm_cosine_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hi := intervalIntegrable_mode r w ha hab
  have hj := intervalIntegrable_mode r (-w) ha hab
  simp_rw [cosine_eq_modes]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi hj, norm_div]
  have hp := norm_integral_le r hw ha hab hsep
  have hn := norm_integral_le r (neg_ne_zero.mpr hw) ha hab
    (show 2 * |r.im| ≤ |-w| * a by simpa only [abs_neg] using hsep)
  simp only [abs_neg] at hn
  norm_num only [norm_ofNat]
  have h := (norm_add_le (∫ x : ℝ in a..b, mode r w x)
    (∫ x : ℝ in a..b, mode r (-w) x)).trans (add_le_add hp hn)
  linarith

end
end RiemannGaussian.OscillatoryPowerPrimitive
