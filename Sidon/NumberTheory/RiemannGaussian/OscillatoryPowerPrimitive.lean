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
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Taylor
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
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Hermitian
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
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Floor
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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Probability.Moments.ComplexMGF
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
