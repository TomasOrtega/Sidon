/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaLogInterval (n : ℕ) : Set ℝ :=
  Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2))

def pairedEtaLogSupport : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval n

def pairedEtaLogMeasure : Measure ℝ :=
  volume.restrict pairedEtaLogSupport

theorem pairwise_disjoint_pairedEtaLogInterval :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m)) := by
  suffices hordered : ∀ {n m : ℕ}, n < m →
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m) by
    intro n m hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact hordered hnm
    · exact (hordered hmn).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t htn htm
  have harg : (2 : ℝ) * n + 2 < 2 * m + 1 := by
    exact_mod_cast (show 2 * n + 2 < 2 * m + 1 by omega)
  have hlog : Real.log (2 * n + 2) < Real.log (2 * m + 1) :=
    Real.log_lt_log (by positivity) harg
  exact (not_lt_of_ge htn.2) (hlog.trans htm.1)

theorem pairedEtaLogMeasure_eq_sum_restrict :
    pairedEtaLogMeasure =
      Measure.sum fun n : ℕ ↦ volume.restrict (pairedEtaLogInterval n) := by
  unfold pairedEtaLogMeasure pairedEtaLogSupport
  exact Measure.restrict_iUnion
    pairwise_disjoint_pairedEtaLogInterval
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

def pairedEtaLaplaceInterval (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
    Complex.exp (-s * t)

def pairedEtaLaplacePartition (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaLaplaceInterval s n

theorem summable_pairedEtaLaplaceInterval
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaLaplaceInterval s) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hsum := (summable_pairedEtaCoreSummand hs).div_const s
  apply hsum.congr
  intro n
  rw [pairedEtaCoreSummand_eq_mul_logLaplaceInterval]
  simp [pairedEtaLaplaceInterval, hs0]

theorem summable_pairedEtaTiltedMassInterval
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t)) := by
  have hcomplex : Summable (pairedEtaLaplaceInterval (sigma : ℂ)) :=
    summable_pairedEtaLaplaceInterval (by simpa using hsigma)
  have hre := Complex.reCLM.summable hcomplex
  apply hre.congr
  intro n
  simpa [pairedEtaLaplaceInterval] using
    (pairedEtaFiniteLaplaceInterval_re sigma 0 n)

theorem integrable_exp_neg_mul_pairedEtaLogMeasure
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      pairedEtaLogMeasure := by
  rw [pairedEtaLogMeasure_eq_sum_restrict]
  apply integrable_sum_measure
  · intro n
    have hcont : Continuous (fun t : ℝ ↦ Complex.exp (-s * t)) := by
      fun_prop
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (hcont.intervalIntegrable _ _)
  · have hnorm := summable_pairedEtaTiltedMassInterval hs
    apply hnorm.congr
    intro n
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    unfold pairedEtaLogInterval
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]

theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) =
      pairedEtaLaplacePartition s := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure hs
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogMeasure_eq_sum_restrict,
    integral_sum_measure hint]
  unfold pairedEtaLaplacePartition pairedEtaLaplaceInterval
    pairedEtaLogInterval
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos n).le).symm

theorem pairedEtaCore_eq_mul_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s = s * pairedEtaLaplacePartition s := by
  unfold pairedEtaCore pairedEtaLaplacePartition
  calc
    ∑' n : ℕ, pairedEtaCoreSummand s n =
        ∑' n : ℕ, s * pairedEtaLaplaceInterval s n := by
      apply tsum_congr
      intro n
      exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n
    _ = s * ∑' n : ℕ, pairedEtaLaplaceInterval s n :=
      (summable_pairedEtaLaplaceInterval hs).tsum_mul_left s

def pairedEtaTiltedCosineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.cos (y * t)
    ∂pairedEtaLogMeasure

def pairedEtaTiltedSineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.sin (y * t)
    ∂pairedEtaLogMeasure

theorem integrable_pairedEtaTiltedCosineKernel
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ ↦
      Real.exp (-sigma * t) * Real.cos (y * t))
      pairedEtaLogMeasure := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  apply hint.re.congr
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem pairedEtaTiltedCosineMoment_zero_pos
    (sigma : ℝ) (hsigma : 0 < sigma) :
    0 < pairedEtaTiltedCosineMoment sigma 0 := by
  have hint := integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  simp only [zero_mul, Real.cos_zero, mul_one] at hint
  unfold pairedEtaTiltedCosineMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [pairedEtaLogMeasure_eq_sum_restrict, integral_sum_measure hint]
  have hsum := summable_pairedEtaTiltedMassInterval hsigma
  calc
    0 < ∑' n : ℕ,
        ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Real.exp (-sigma * t) := by
      apply hsum.tsum_pos
      · intro n
        exact (intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos n)).le
      · exact intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos 0)
    _ = ∑' n : ℕ,
        ∫ t : ℝ, Real.exp (-sigma * t)
          ∂volume.restrict (pairedEtaLogInterval n) := by
      apply tsum_congr
      intro n
      unfold pairedEtaLogInterval
      exact (intervalIntegral.integral_of_le
        (pairedEtaFiniteLogInterval_pos n).le)

theorem integral_exp_neg_mul_pairedEtaLogMeasure_re
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).re =
      pairedEtaTiltedCosineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have hre :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).re := by
    simpa using integral_re hint
  rw [← hre]
  unfold pairedEtaTiltedCosineMoment
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem integral_exp_neg_mul_pairedEtaLogMeasure_im
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).im =
      -pairedEtaTiltedSineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have him :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).im := by
    simpa using integral_im hint
  rw [← him]
  unfold pairedEtaTiltedSineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_im sigma y t

theorem pairedEtaLaplacePartition_eq_cosine_sub_I_sine
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    pairedEtaLaplacePartition
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      (pairedEtaTiltedCosineMoment sigma y : ℂ) -
        (pairedEtaTiltedSineMoment sigma y : ℂ) * Complex.I := by
  rw [← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)]
  apply Complex.ext
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_re sigma y hsigma]
    norm_num [Complex.mul_re]
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_im sigma y hsigma]
    norm_num [Complex.mul_im]

theorem pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaLaplacePartition rho.1 = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      hre rho.2.2.2, rho.2.1, mul_zero]
  have hmul : rho.1 * pairedEtaLaplacePartition rho.1 = 0 := by
    rw [← pairedEtaCore_eq_mul_laplacePartition hre, hcore]
  exact (mul_eq_zero.mp hmul).resolve_left (by
    intro hrho
    have := congrArg Complex.re hrho
    norm_num at this
    linarith)

theorem pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaTiltedCosineMoment rho.1.re rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment rho.1.re rho.1.im = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hzeroCoordinates :
      pairedEtaLaplacePartition
        (((rho.1.re : ℝ) : ℂ) + ((rho.1.im : ℝ) : ℂ) * Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using
      pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho
  have hsplit :=
    pairedEtaLaplacePartition_eq_cosine_sub_I_sine
      rho.1.re rho.1.im hre
  rw [hzeroCoordinates] at hsplit
  constructor
  · have hreal := congrArg Complex.re hsplit
    norm_num [Complex.mul_re] at hreal
    exact hreal.symm
  · have himag := congrArg Complex.im hsplit
    norm_num [Complex.mul_im] at himag
    exact himag

end

end RiemannGaussian
