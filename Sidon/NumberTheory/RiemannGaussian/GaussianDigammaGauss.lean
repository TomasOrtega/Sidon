/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section

open Filter Set Real Asymptotics MeasureTheory
open scoped Topology

namespace Complex

theorem integrableOn_gammaIntegral_log_kernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (Real.log t * Real.exp (-t))) (Ioi 0) := by
  have hconv :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
      (f := fun x : ℝ => (Real.exp (-x) : ℂ))
      (a := s.re + 1) (b := 0)
      (by
        refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
        exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg))
      (by
        rw [← isBigO_norm_left]
        simp_rw [norm_real, isBigO_norm_left]
        simpa only [neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(s.re + 1))).isBigO)
      (lt_add_one _)
      (by
        simp_rw [neg_zero, rpow_zero]
        refine isBigO_const_of_tendsto
          (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
        rw [(by simp : (1 : ℂ) = Real.exp (-0))]
        exact (continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousWithinAt)
      hs).1
  rw [MellinConvergent] at hconv
  simpa [smul_eq_mul, real_smul] using hconv

end Complex

namespace Complex

def gammaApproxWeight (n : ℕ) (x : ℝ) : ℂ :=
  indicator (Ioc 0 (n : ℝ))
    (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x

theorem mellin_gammaApproxWeight (n : ℕ) (z : ℂ) :
    mellin (gammaApproxWeight n) z =
      ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) := by
  unfold mellin gammaApproxWeight
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) •
          indicator (Ioc 0 (n : ℝ))
            (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x) =
      ∫ x : ℝ in Ioi 0,
        indicator (Ioc 0 (n : ℝ))
          (fun y : ℝ =>
            (((1 - y / n) ^ n : ℝ) : ℂ) *
              (y : ℂ) ^ (z - 1)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc (0 : ℝ) n
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          simp only [smul_eq_mul]
          ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    _ = ∫ x : ℝ in Ioc 0 (n : ℝ),
          (((1 - x / n) ^ n : ℝ) : ℂ) *
            (x : ℂ) ^ (z - 1) := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ))]

theorem mellin_log_gammaApproxWeight (n : ℕ) (z : ℂ) :
    mellin (fun x : ℝ => Real.log x • gammaApproxWeight n x) z =
      ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (z - 1) * Real.log x) := by
  unfold mellin gammaApproxWeight
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) •
          (Real.log x •
            indicator (Ioc 0 (n : ℝ))
              (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x)) =
      ∫ x : ℝ in Ioi 0,
        indicator (Ioc 0 (n : ℝ))
          (fun y : ℝ =>
            (((1 - y / n) ^ n : ℝ) : ℂ) *
              ((y : ℂ) ^ (z - 1) * Real.log y)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc (0 : ℝ) n
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          simp only [smul_eq_mul, real_smul]
          ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx,
            smul_zero, smul_zero]
    _ = ∫ x : ℝ in Ioc 0 (n : ℝ),
          (((1 - x / n) ^ n : ℝ) : ℂ) *
            ((x : ℂ) ^ (z - 1) * Real.log x) := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ))]

theorem hasDerivAt_mellin_gammaApproxWeight
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (mellin (gammaApproxWeight n))
      (mellin (fun x : ℝ =>
        Real.log x • gammaApproxWeight n x) s) s := by
  have hw_int : IntegrableOn (gammaApproxWeight n) (Ioi 0) := by
    unfold gammaApproxWeight
    change IntegrableOn
      (indicator (Ioc 0 (n : ℝ))
        (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ))) (Ioi 0)
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc,
      IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      ← IntegrableOn,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by positivity : (0 : ℝ) ≤ n)]
    exact Continuous.intervalIntegrable (μ := volume) (by fun_prop : Continuous
      (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ))) 0 (n : ℝ)
  have hw_top : gammaApproxWeight n =O[atTop]
      (fun x : ℝ => x ^ (-(s.re + 1))) := by
    have hzero : gammaApproxWeight n =ᶠ[atTop]
        (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [eventually_gt_atTop (n : ℝ)] with x hx
      unfold gammaApproxWeight
      rw [indicator_of_notMem (notMem_Ioc_of_gt hx)]
    exact (isBigO_zero (fun x : ℝ => x ^ (-(s.re + 1))) atTop).congr'
      hzero.symm EventuallyEq.rfl
  have hw_tend : Tendsto (gammaApproxWeight n)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    let p : ℝ → ℂ := fun x : ℝ => (((1 - x / n) ^ n : ℝ) : ℂ)
    have hp : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      have hp' : Tendsto p (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) := by
        have hc : ContinuousAt p 0 := by fun_prop
        change Tendsto p (𝓝 (0 : ℝ)) (𝓝 (p 0)) at hc
        have hp0 : p 0 = 1 := by simp [p]
        rw [hp0] at hc
        exact hc
      exact hp'.mono_left nhdsWithin_le_nhds
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have heq : gammaApproxWeight n =ᶠ[𝓝[>] (0 : ℝ)] p := by
      filter_upwards [eventually_mem_nhdsWithin,
        (eventually_lt_nhds hnpos).filter_mono nhdsWithin_le_nhds] with x hx hxn
      have hxmem : x ∈ Ioc (0 : ℝ) (n : ℝ) := ⟨hx, hxn.le⟩
      unfold gammaApproxWeight p
      rw [indicator_of_mem hxmem]
    exact hp.congr' heq.symm
  have hw_bot : gammaApproxWeight n =O[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    simp_rw [neg_zero, rpow_zero]
    exact isBigO_const_of_tendsto hw_tend one_ne_zero
  exact (mellin_hasDerivAt_of_isBigO_rpow
    hw_int.locallyIntegrableOn hw_top (lt_add_one _)
    hw_bot hs).2

theorem hasDerivAt_approx_Gamma_integral
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt
      (fun z : ℂ => ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          (x : ℂ) ^ (z - 1))
      (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) s := by
  have h := hasDerivAt_mellin_gammaApproxWeight hs hn
  rw [mellin_log_gammaApproxWeight] at h
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun z => (mellin_gammaApproxWeight n z).symm)

end Complex

namespace Complex

lemma add_natCast_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    s + j ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hjre : ((j : ℂ).re) = (j : ℝ) := by norm_num
  rw [add_re, hjre, zero_re] at hre
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  linarith

theorem GammaSeq_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : n ≠ 0) : GammaSeq s n ≠ 0 := by
  unfold GammaSeq
  apply div_ne_zero
  · apply mul_ne_zero
    · exact cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
    · exact_mod_cast Nat.factorial_ne_zero n
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact add_natCast_ne_zero_of_re_pos hs j

theorem logDeriv_GammaSeq {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z : ℂ => GammaSeq z n) s =
      Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfacC : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfactor : ∀ j ∈ Finset.range (n + 1), s + (j : ℂ) ≠ 0 := by
    intro j hj
    exact add_natCast_ne_zero_of_re_pos hs j
  unfold GammaSeq
  rw [logDeriv_fun_div s]
  · rw [logDeriv_fun_mul s]
    · rw [logDeriv_fun_prod hfactor]
      · simp only [logDeriv_apply]
        rw [((hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
          (Or.inl hnC)).hasDerivAt.deriv)]
        simp only [deriv_const, zero_div, deriv_add_const, deriv_id'']
        rw [mul_div_cancel_left₀ _ (cpow_ne_zero_iff.mpr (Or.inl hnC))]
        simp only [add_zero, inv_eq_one_div]
      · intro j hj
        fun_prop
    · exact cpow_ne_zero_iff.mpr (Or.inl hnC)
    · exact hfacC
    · exact (hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
        (Or.inl hnC)).hasDerivAt.differentiableAt
    · fun_prop
  · exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) hfacC
  · exact Finset.prod_ne_zero_iff.mpr hfactor
  · exact ((hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
      (Or.inl hnC)).hasDerivAt.differentiableAt.mul
        (by fun_prop : DifferentiableAt ℂ
          (fun _ : ℂ => ((Nat.factorial n : ℕ) : ℂ)) s))
  · fun_prop

end Complex

namespace Complex

theorem hasDerivAt_GammaSeq_log_integral
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun z : ℂ => GammaSeq z n)
      (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) s := by
  have h := hasDerivAt_approx_Gamma_integral hs hn
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  apply h.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact GammaSeq_eq_approx_Gamma_integral hz hn

theorem approx_Gamma_log_integral_eq_GammaSeq_mul
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ x : ℝ in 0..n,
      (((1 - x / n) ^ n : ℝ) : ℂ) *
        ((x : ℂ) ^ (s - 1) * Real.log x)) =
      GammaSeq s n *
        (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹) := by
  let F : ℂ → ℂ := fun z => GammaSeq z n
  have hderiv := hasDerivAt_GammaSeq_log_integral hs hn
  have hne : F s ≠ 0 := GammaSeq_ne_zero_of_re_pos hs hn
  have hlog := logDeriv_GammaSeq hs hn
  change logDeriv F s = _ at hlog
  calc
    (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) = deriv F s := hderiv.deriv.symm
    _ = F s * logDeriv F s := by
      rw [logDeriv_apply]
      field_simp
    _ = GammaSeq s n *
        (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹) := by
      rw [hlog]

theorem hasDerivAt_Gamma_integral_log_kernel
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma
      (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) s := by
  have h := hasDerivAt_GammaIntegral hs
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  exact h.congr_of_eventuallyEq (by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact Gamma_eq_integral hz)

end Complex

namespace Complex

theorem approx_Gamma_integral_log_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x))
      atTop
      (𝓝 <| ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) := by
  let f : ℕ → ℝ → ℂ := fun n =>
    indicator (Ioc 0 (n : ℝ)) fun x : ℝ =>
      (((1 - x / n) ^ n : ℝ) : ℂ) *
        ((x : ℂ) ^ (s - 1) * Real.log x)
  let g : ℝ → ℝ := fun x =>
    ‖(x : ℂ) ^ (s - 1) *
      (Real.log x * Real.exp (-x))‖
  have f_meas : ∀ n : ℕ,
      AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    apply Measurable.aestronglyMeasurable
    unfold f
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_Ioc
  have g_ible : Integrable g (volume.restrict (Ioi 0)) := by
    exact (integrableOn_gammaIntegral_log_kernel hs).norm
  have f_tends : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      Tendsto (fun n : ℕ => f n x) atTop
        (𝓝 <| (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ n : ℕ in atTop,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
              ((x : ℂ) ^ (s - 1) * Real.log x) = f n x
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · have hreal : Tendsto (fun n : ℕ => (1 - x / n) ^ n)
          atTop (𝓝 (Real.exp (-x))) := by
        convert Real.tendsto_one_add_div_pow_exp (-x) using 1
        ext n
        rw [neg_div, ← sub_eq_add_neg]
      have hcomplex : Tendsto
          (fun n : ℕ => (((1 - x / n) ^ n : ℝ) : ℂ))
          atTop (𝓝 (Real.exp (-x) : ℂ)) :=
        (continuous_ofReal.tendsto _).comp hreal
      convert hcomplex.mul_const
        ((x : ℂ) ^ (s - 1) * Real.log x) using 1
      congr 1
      ring
  have f_bound : ∀ n : ℕ,
      ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), ‖f n x‖ ≤ g x := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi, f] at hx ⊢
    rcases lt_or_ge (n : ℝ) x with hxn | hxn
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero]
      exact norm_nonneg _
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩)]
      unfold g
      have hbase : 0 ≤ 1 - x / (n : ℝ) :=
        sub_nonneg.mpr (div_le_one_of_le₀ hxn (by positivity))
      have hcoeff : 0 ≤ (1 - x / (n : ℝ)) ^ n := pow_nonneg hbase _
      have hfactor : 0 ≤ ‖(x : ℂ) ^ (s - 1)‖ * |Real.log x| :=
        mul_nonneg (norm_nonneg _) (abs_nonneg _)
      have hpow := one_sub_div_pow_le_exp_neg hxn
      calc
        ‖(((1 - x / n) ^ n : ℝ) : ℂ) *
            ((x : ℂ) ^ (s - 1) * Real.log x)‖ =
            (1 - x / n) ^ n *
              (‖(x : ℂ) ^ (s - 1)‖ * |Real.log x|) := by
          rw [norm_mul, Complex.norm_of_nonneg hcoeff, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ Real.exp (-x) *
              (‖(x : ℂ) ^ (s - 1)‖ * |Real.log x|) :=
          mul_le_mul_of_nonneg_right hpow hfactor
        _ = ‖(x : ℂ) ^ (s - 1) *
              (Real.log x * Real.exp (-x))‖ := by
          rw [norm_mul, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          ring
  convert!
    tendsto_integral_of_dominated_convergence g f_meas g_ible f_bound
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
  ext n
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ)),
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

end Complex

namespace Complex

theorem digamma_tendsto_euler {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹)
      atTop (𝓝 (digamma s)) := by
  let I : ℕ → ℂ := fun n => ∫ x : ℝ in 0..n,
    (((1 - x / n) ^ n : ℝ) : ℂ) *
      ((x : ℂ) ^ (s - 1) * Real.log x)
  have hI : Tendsto I atTop (𝓝 (deriv Gamma s)) := by
    have hlim := approx_Gamma_integral_log_tendsto hs
    have hderiv := hasDerivAt_Gamma_integral_log_kernel hs
    change Tendsto I atTop
      (𝓝 <| ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) at hlim
    rw [← hderiv.deriv] at hlim
    exact hlim
  have hquot := hI.div (GammaSeq_tendsto_Gamma s)
    (Gamma_ne_zero_of_re_pos hs)
  have htarget : deriv Gamma s / Gamma s = digamma s := by
    rw [digamma_def, logDeriv_apply]
  rw [htarget] at hquot
  apply hquot.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hne := GammaSeq_ne_zero_of_re_pos hs hn
  have hprod := approx_Gamma_log_integral_eq_GammaSeq_mul hs hn
  change I n / GammaSeq s n =
    Complex.log (n : ℂ) -
      ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹
  dsimp only [I]
  rw [hprod]
  field_simp

end Complex

namespace RiemannGaussian

open Filter MeasureTheory Topology Set
open scoped BigOperators Topology

end RiemannGaussian
