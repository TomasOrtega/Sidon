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
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
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
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
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

public import Mathlib.Analysis.Complex.HalfPlane

@[expose] public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaCoreSummand (s : ℂ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

def pairedEtaCore (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaCoreSummand s n

lemma pairedEtaCoreSummand_eq_integral (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
        ((x : ℂ) ^ (-s - 1)) := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hderiv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) x := by
    by_cases hs : s = 0
    · subst s
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ)))
    · convert hasDerivAt_ofReal_cpow_const (x := x)
        (by
          rw [uIcc_of_le (by
            dsimp [a, b]
            exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
          exact (ha.trans_le hx.1).ne')
        (neg_ne_zero.mpr hs) using 1
  have hint : IntervalIntegrable
      (fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hp : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (uIcc a b) := by
      apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
      intro x hx
      rw [uIcc_of_le (by
        dsimp [a, b]
        exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
      exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)
    exact continuousOn_const.mul hp
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hfund
  dsimp [pairedEtaCoreSummand, a, b]
  have hs : (-s) *
        (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1)) =
      ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
    simpa only using hfund
  calc
    ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) =
        -((-s) *
          (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
            (x : ℂ) ^ (-s - 1))) := by rw [hs]; ring
    _ = s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1) := by ring

lemma norm_pairedEtaCoreSummand_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖pairedEtaCoreSummand s n‖ ≤
      ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega)
  rw [pairedEtaCoreSummand_eq_integral, norm_mul]
  have hIntegral :
      ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        a ^ (-s.re - 1) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
    simp only [neg_re, sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha hx.1.le (by linarith)
  calc
    ‖s‖ * ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        ‖s‖ * (a ^ (-s.re - 1) * |b - a|) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ = ‖s‖ * a ^ (-s.re - 1) := by
      have hba : b - a = 1 := by
        dsimp [a, b]
        push_cast
        ring
      rw [hba, abs_one]
      ring
    _ = ‖s‖ * (a ^ (s.re + 1))⁻¹ := by
      rw [← Real.rpow_neg ha.le]
      congr 2
      ring
    _ = ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := rfl

lemma summable_pairedEtaCoreSummand {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaCoreSummand s) := by
  have hfull : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (s.re + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (s.re + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  apply Summable.of_norm_bounded (hodd.mul_left ‖s‖)
  exact norm_pairedEtaCoreSummand_le hs

lemma differentiableOn_pairedEtaCore :
    DifferentiableOn ℂ pairedEtaCore {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let delta : ℝ := z.re / 2
  let radius : ℝ := z.re / 2
  let K : ℝ := ‖z‖ + radius
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (delta + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (delta + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hbase.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have hmajor : Summable
      (fun n : ℕ => K *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) :=
    hodd.mul_left K
  have hterms (n : ℕ) :
      DifferentiableOn ℂ (fun w : ℂ => pairedEtaCoreSummand w n)
        (Metric.ball z radius) := by
    unfold pairedEtaCoreSummand
    have hleft : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)))
    have hright : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)))
    exact (hleft.sub hright).differentiableOn
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball z radius) :
      ‖pairedEtaCoreSummand w n‖ ≤
        K * ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹ := by
    have hdist : dist w z < radius := by simpa [Metric.mem_ball] using hw
    have hreNorm : |w.re - z.re| ≤ dist w z := by
      calc
        |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ = dist w z := by rw [dist_eq_norm]
    have hwre : delta < w.re := by
      dsimp [delta, radius] at *
      linarith [neg_le_abs (w.re - z.re)]
    have hwNorm : ‖w‖ ≤ K := by
      calc
        ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ K := by dsimp [K]; linarith
    have hraw := norm_pairedEtaCoreSummand_le (s := w) (hdelta.trans hwre) n
    let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hpow : a ^ (-w.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [← Real.rpow_neg ha0, show -(w.re + 1) = -w.re - 1 by ring] at hraw
    rw [← Real.rpow_neg ha0, show -(delta + 1) = -delta - 1 by ring]
    calc
      ‖pairedEtaCoreSummand w n‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
        simpa [a] using hraw
      _ ≤ K * a ^ (-delta - 1) :=
        mul_le_mul hwNorm hpow (Real.rpow_nonneg ha0 _) hK
  have hlocal : DifferentiableOn ℂ pairedEtaCore (Metric.ball z radius) := by
    unfold pairedEtaCore
    exact Complex.differentiableOn_tsum_of_summable_norm
      hmajor hterms Metric.isOpen_ball hbound
  exact (hlocal.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hradius))).differentiableWithinAt

lemma analyticOnNhd_pairedEtaCore :
    AnalyticOnNhd ℂ pairedEtaCore {s : ℂ | 0 < s.re} :=
  differentiableOn_pairedEtaCore.analyticOnNhd (Complex.isOpen_re_gt 0)

lemma hasSum_nat_add_one_cpow_neg_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s))
      (riemannZeta s) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 : ℝ)) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hs
  have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨1, by norm_num⟩
  rw [hone, HurwitzZeta.hurwitzZeta_zero] at h
  simpa [Complex.cpow_neg] using h

lemma pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)
  have hfull : HasSum f (riemannZeta s) := by
    simpa [f] using hasSum_nat_add_one_cpow_neg_riemannZeta hs
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel h))
  have hevenSum : HasSum (fun n : ℕ => f (2 * n + 1))
      ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    apply (hfull.mul_left ((2 : ℂ) ^ (-s))).congr_fun
    intro n
    dsimp [f]
    calc
      ((((2 * n + 1 + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) =
          ((((2 : ℝ) * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) ^ (-s) := by
        congr 2
        push_cast
        ring
      _ = (((2 : ℝ) : ℂ)) ^ (-s) *
          (((((n + 1 : ℕ) : ℝ)) : ℂ)) ^ (-s) := by
        simpa only [Complex.ofReal_mul] using
          (Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ))
            (b := ((n + 1 : ℕ) : ℝ)) (by norm_num) (by positivity) (-s))
      _ = (2 : ℂ) ^ (-s) * (((n + 1 : ℕ) : ℂ)) ^ (-s) := by norm_num
  have hsplit :
      (∑' n : ℕ, f (2 * n)) +
          (2 : ℂ) ^ (-s) * riemannZeta s = riemannZeta s := by
    exact (HasSum.even_add_odd hodd.hasSum hevenSum).unique hfull
  have hpaired : pairedEtaCore s =
      (∑' n : ℕ, f (2 * n)) -
        ∑' n : ℕ, f (2 * n + 1) := by
    unfold pairedEtaCore
    rw [← hodd.tsum_sub heven]
    apply tsum_congr
    intro n
    dsimp [pairedEtaCoreSummand, f]
  rw [hpaired, hevenSum.tsum_eq]
  linear_combination hsplit

def pairedEtaUpperRightDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ 0 < s.im}

lemma isOpen_pairedEtaUpperRightDomain : IsOpen pairedEtaUpperRightDomain := by
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_im_gt 0)

lemma isPreconnected_pairedEtaUpperRightDomain :
    IsPreconnected pairedEtaUpperRightDomain := by
  apply Convex.isPreconnected
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    {s : ℂ} (hsre : 0 < s.re) (hsim : 0 < s.im) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  have hlhs : AnalyticOnNhd ℂ pairedEtaCore pairedEtaUpperRightDomain :=
    analyticOnNhd_pairedEtaCore.mono (by
      intro w hw
      exact hw.1)
  have hrhsDiff : DifferentiableOn ℂ rhs pairedEtaUpperRightDomain := by
    intro w hw
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    have hwone : w ≠ 1 := by
      intro h
      subst w
      simpa [pairedEtaUpperRightDomain] using hw.2
    exact hfactor.mul (differentiableAt_riemannZeta hwone) |>.differentiableWithinAt
  have hrhs : AnalyticOnNhd ℂ rhs pairedEtaUpperRightDomain :=
    hrhsDiff.analyticOnNhd isOpen_pairedEtaUpperRightDomain
  let z0 : ℂ := 2 + Complex.I
  have hz0 : z0 ∈ pairedEtaUpperRightDomain := by
    simp [z0, pairedEtaUpperRightDomain]
  have hevent : pairedEtaCore =ᶠ[𝓝 z0] rhs := by
    filter_upwards [
      (Complex.isOpen_re_gt 1).mem_nhds
        (show 1 < z0.re by simp [z0])] with w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re hw
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs
    isPreconnected_pairedEtaUpperRightDomain hz0 hevent ⟨hsre, hsim⟩

end

end RiemannGaussian
