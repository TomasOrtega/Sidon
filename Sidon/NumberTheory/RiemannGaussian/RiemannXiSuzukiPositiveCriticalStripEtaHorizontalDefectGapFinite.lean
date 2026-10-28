module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

@[expose] public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaLogTailSupport (N : ℕ) : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval (n + N)

def pairedEtaLogTailMeasure (N : ℕ) : Measure ℝ :=
  volume.restrict (pairedEtaLogTailSupport N)

theorem pairwise_disjoint_pairedEtaLogInterval_natAdd (N : ℕ) :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval (n + N))
        (pairedEtaLogInterval (m + N))) := by
  intro n m hne
  apply pairwise_disjoint_pairedEtaLogInterval
  omega

theorem pairedEtaLogTailMeasure_eq_sum_restrict (N : ℕ) :
    pairedEtaLogTailMeasure N =
      Measure.sum fun n : ℕ ↦
        volume.restrict (pairedEtaLogInterval (n + N)) := by
  unfold pairedEtaLogTailMeasure pairedEtaLogTailSupport
  exact Measure.restrict_iUnion
    (pairwise_disjoint_pairedEtaLogInterval_natAdd N)
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

theorem pairedEtaLogTailSupport_subset_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailSupport N ⊆ Ioi (Real.log (2 * N + 1)) := by
  intro t ht
  rw [pairedEtaLogTailSupport, mem_iUnion] at ht
  obtain ⟨n, hn⟩ := ht
  have harg : (2 : ℝ) * N + 1 ≤ 2 * (n + N) + 1 := by
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (n + N) + 1 by omega)
  have hlog : Real.log (2 * N + 1) ≤
      Real.log (2 * (n + N) + 1) :=
    Real.log_le_log (by positivity) harg
  exact hlog.trans_lt (by simpa [Nat.cast_add] using hn.1)

theorem pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi (Real.log (2 * N + 1))) := by
  unfold pairedEtaLogTailMeasure
  exact Measure.restrict_mono
    (pairedEtaLogTailSupport_subset_Ioi_log_odd N) le_rfl

theorem integrable_exp_neg_mul_pairedEtaLogTailMeasure
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (pairedEtaLogTailMeasure N) := by
  have hfull := integrableOn_exp_mul_complex_Ioi (a := -s) (by
    norm_num
    linarith) (Real.log (2 * N + 1))
  have hfull' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (volume.restrict (Ioi (Real.log (2 * N + 1)))) := by
    apply hfull.congr
    filter_upwards with t
    congr 1
  exact hfull'.mono_measure
    (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)

theorem integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) =
      ∑' n : ℕ, pairedEtaLaplaceInterval s (n + N) := by
  have hint := integrable_exp_neg_mul_pairedEtaLogTailMeasure hs N
  rw [pairedEtaLogTailMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogTailMeasure_eq_sum_restrict, integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLaplaceInterval pairedEtaLogInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos (n + N)).le).symm

theorem pairedEtaCore_sub_partialSum_eq_mul_tailIntegral
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N := by
  have hsplit :=
    (summable_pairedEtaLaplaceInterval hs).sum_add_tsum_nat_add N
  change pairedEtaFiniteLaplacePartition N s +
      (∑' n : ℕ, pairedEtaLaplaceInterval s (n + N)) =
    pairedEtaLaplacePartition s at hsplit
  rw [pairedEtaCore_eq_mul_laplacePartition hs,
    pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition,
    integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd hs]
  rw [← hsplit]
  ring

theorem norm_cexp_neg_mul_eq_exp_neg_re_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * t)‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]

theorem integral_exp_neg_mul_Ioi_log_odd
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
      Real.exp (-sigma * t)) =
      ((2 * N + 1 : ℕ) : ℝ) ^ (-sigma) / sigma := by
  rw [integral_exp_mul_Ioi (a := -sigma) (by linarith)]
  rw [neg_div_neg_eq]
  have hbase : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [Real.rpow_def_of_pos hbase, hcast]
  apply congrArg (fun x : ℝ ↦ x / sigma)
  apply congrArg Real.exp
  ring

theorem norm_pairedEtaCore_sub_partialSum_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
  rw [pairedEtaCore_sub_partialSum_eq_mul_tailIntegral hs, norm_mul]
  have hrealIntegrable : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-s.re * t))
      (Ioi (Real.log (2 * N + 1))) := by
    have h := integrableOn_exp_mul_Ioi (a := -s.re) (by linarith)
      (Real.log (2 * N + 1))
    simpa only [neg_mul] using h
  have hnormIntegral :
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N := by
    calc
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
          ∫ t : ℝ, ‖Complex.exp (-s * t)‖
            ∂pairedEtaLogTailMeasure N :=
        norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N := by
        apply integral_congr_ae
        filter_upwards with t
        exact norm_cexp_neg_mul_eq_exp_neg_re_mul s t
  have hmeasureIntegral :
      (∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N) ≤
        ∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t) := by
    exact integral_mono_measure
      (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)
      (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
      hrealIntegrable
  calc
    ‖s‖ *
        ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ‖s‖ *
          (∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N) :=
      mul_le_mul_of_nonneg_left hnormIntegral (norm_nonneg s)
    _ ≤ ‖s‖ *
        (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t)) :=
      mul_le_mul_of_nonneg_left hmeasureIntegral (norm_nonneg s)
    _ = ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
      rw [integral_exp_neg_mul_Ioi_log_odd hs]

theorem tendsto_pairedEtaOddEndpoint_rpow_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ ↦ (2 : ℝ) * N + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  convert (tendsto_rpow_neg_atTop hs).comp hbase using 1
  funext N
  norm_num

end

end RiemannGaussian
