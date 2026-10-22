/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.OpenMapping
import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscCanonicalBounds
import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscLogarithm
import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscSignedDerivative

namespace RiemannGaussian.AnalyticDiscBoundaryMoment
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open RiemannGaussian.AnalyticDiscCanonicalBounds RiemannGaussian.AnalyticDiscSignedDerivative
open scoped Topology

def moment (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  Real.circleAverage (fun z : ℂ ↦ (2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)) 0 R

def extension (f : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage
    (fun z : ℂ ↦ herglotzRieszKernel 0 w z * (Real.log ‖f z‖ : ℂ)) 0 R

theorem circleIntegrable_log_norm {f : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, f z ≠ 0) :
    CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 R := by
  exact ContinuousOn.circleIntegrable hR
    ((hf.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz))).mono
      sphere_subset_closedBall)

theorem extension_re {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, f z ≠ 0) {w : ℂ} (hw : w ∈ ball 0 R) :
    (extension f R w).re = Real.log ‖f w‖ := by
  have hh : InnerProductSpace.HarmonicOnNhd (fun z ↦ Real.log ‖f z‖) (closedBall 0 R) :=
    fun z hz ↦ (hf z hz).harmonicAt_log_norm (hne z hz)
  have hw' : w ∉ sphere (0 : ℂ) |R| := by
    intro hs
    have hlt : dist w 0 < R := hw
    have heq : dist w 0 = |R| := hs
    rw [abs_of_pos (pos_of_mem_ball hw)] at heq
    linarith
  simpa only [extension, smul_eq_mul] using
    (re_circleAverage_herglotzRieszKernel_smul
      (circleIntegrable_log_norm (pos_of_mem_ball hw).le hf hne) hw').trans
      (hh.circleAverage_re_herglotzRieszKernel_smul hw)

theorem logDeriv_eq_moment {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) : logDeriv g 0 = moment g R := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hnot : ∀ w ∈ ball (0 : ℂ) R, w ∉ sphere (0 : ℂ) |R| := by
    intro w hw hs
    have hlt : dist w 0 < R := hw
    have heq : dist w 0 = |R| := hs
    rw [abs_of_pos hR] at heq
    linarith
  have hcc : CircleIntegrable (fun z ↦ (Real.log ‖g z‖ : ℂ)) 0 R := by
    exact ContinuousOn.circleIntegrable hR.le
      ((Complex.ofRealCLM.continuous.comp_continuousOn
        (hg.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz)))).mono
        sphere_subset_closedBall)
  have hH : HasDerivAt (extension g R) (moment g R) 0 := by
    simpa only [extension, moment, sub_zero, smul_eq_mul] using!
      hasDerivAt_circleAverage_herglotzRieszKernel_smul hcc (hnot 0 hzero)
  have hHa : AnalyticOnNhd ℂ (extension g R) (ball 0 R) := by
    simpa only [extension, smul_eq_mul] using!
      (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hcc).mono hnot
  obtain ⟨L, hL0, hL⟩ := AnalyticDiscLogarithm.exists_logarithm hg hne
  have hLa : AnalyticOnNhd ℂ L (ball 0 R) :=
    (show DifferentiableOn ℂ L (ball 0 R) from
      fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hLre {z : ℂ} (hz : z ∈ ball 0 R) :
      (L z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
    have he := congrArg norm (AnalyticDiscLogarithm.exp_mul_center hR hg hne hL0 hL hz)
    rw [norm_mul, Complex.norm_exp] at he
    have hl := congrArg Real.log he
    rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr
      (hne 0 (mem_closedBall_self hR.le))), Real.log_exp] at hl
    linarith
  obtain ⟨c, heq⟩ := (hHa.sub hLa).eq_const_of_re_eq_const
    (c₀ := Real.log ‖g 0‖)
    (fun z hz ↦ by simp only [Pi.sub_apply, Complex.sub_re, extension_re hg hne hz, hLre hz]; ring)
    isOpen_ball (isConnected_ball hR)
  have hevent : (fun z ↦ extension g R z - L z) =ᶠ[𝓝 0] fun _ ↦ c :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hR) heq
  have hzderiv : HasDerivAt (fun z ↦ extension g R z - L z) 0 0 :=
    (hasDerivAt_const 0 c).congr_of_eventuallyEq hevent
  have hd := (hH.sub (hL 0 hzero)).unique hzderiv
  exact (sub_eq_zero.mp hd).symm

theorem moment_re {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    (moment f R).re = 2 / R ^ 2 *
      Real.circleAverage (fun z : ℂ ↦ z.re * Real.log ‖f z‖) 0 R := by
  have hz0 : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz he
    subst z
    simp only [mem_sphere, dist_self] at hz
    linarith
  have hk : ContinuousOn (fun z : ℂ ↦ 2 * z / z ^ 2) (sphere 0 R) :=
    (continuous_const.mul continuous_id).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz ↦ pow_ne_zero 2 (hz0 z hz))
  have hl := hf.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz))
  have hp : CircleIntegrable
      (fun z : ℂ ↦ (2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (hk.mul (Complex.ofRealCLM.continuous.comp_continuousOn hl))
  calc
    (moment f R).re = Real.circleAverage
        (fun z : ℂ ↦ ((2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)).re) 0 R := by
      exact (Complex.reCLM.circleAverage_comp_comm hp).symm
    _ = Real.circleAverage (fun z : ℂ ↦ (2 / R ^ 2) * (z.re * Real.log ‖f z‖)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hR] at hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
      have he : 2 * z / z ^ 2 = 2 / z := by field_simp
      dsimp only
      rw [he]
      norm_num [Complex.mul_re, Complex.div_re, Complex.normSq_eq_norm_sq, hn]
      ring
    _ = _ := by
      simpa only [smul_eq_mul] using!
        (Real.circleAverage_fun_smul (a := 2 / R ^ 2)
          (f := fun z : ℂ ↦ z.re * Real.log ‖f z‖) (c := 0) (R := R))

theorem neg_moment_re {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    (-moment f R).re = 2 / R ^ 2 *
      Real.circleAverage (fun z : ℂ ↦ -z.re * Real.log ‖f z‖) 0 R := by
  rw [Complex.neg_re, moment_re hR hf hne]
  have he : Real.circleAverage (fun z : ℂ ↦ -z.re * Real.log ‖f z‖) 0 R =
      -Real.circleAverage (fun z : ℂ ↦ z.re * Real.log ‖f z‖) 0 R := by
    simpa [smul_eq_mul, neg_mul] using!
      (Real.circleAverage_fun_smul (a := (-1 : ℝ))
        (f := fun z : ℂ ↦ z.re * Real.log ‖f z‖) (c := 0) (R := R))
  rw [he]
  ring

theorem logDeriv_eq_moment_add_divisor {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    logDeriv f 0 = moment f R + ∑ᶠ a, divisor f (ball 0 R) a • kernel R a := by
  obtain ⟨g, D⟩ := exists_decomp hR hf hf0
  rw [logDeriv_center_eq hR hf hf0 hs D, logDeriv_eq_moment hR D.analyticOnNhd D.ne_zero]
  congr 1
  unfold moment
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hR] at hz
  dsimp only
  rw [norm_eq_on_sphere hR hf hs D hz]

end
end RiemannGaussian.AnalyticDiscBoundaryMoment
