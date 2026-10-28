module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscBoundaryMoment
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscSignedBoundary
public import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerReciprocalAllowance
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneFullDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneJensen
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneSignedBound

@[expose] public section

namespace RiemannGaussian.ZetaNearOneAngularBound
noncomputable section
open Complex Filter Metric Set MeromorphicOn RiemannGaussian.ZetaNearOneLocalDisc RiemannGaussian.ZetaNearOneLogProfile
open RiemannGaussian.DerivativeOrderComparison RiemannGaussian.ZetaNearOneCanonical RiemannGaussian.ZetaNearOneJensen RiemannGaussian.ZetaNearOneSignedBound
open RiemannGaussian.AnalyticDiscBoundaryMoment
open scoped Topology

theorem right_arc_lower (t : ℝ) {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 ≤ z.re) :
    -Real.log ‖translated x t z‖ ≤ Real.log (1 + 1 / x) := by
  have hre : (center x t + z).re = 1 + x + z.re := by simp [ZetaNearOneLocalDisc.center]
  have hs : 1 < (center x t + z).re := by rw [hre]; linarith
  have hden : x ≤ (center x t + z).re - 1 := by rw [hre]; linarith
  change -Real.log ‖riemannZeta (z + center x t)‖ ≤ _
  rw [add_comm z (center x t)]
  apply (ZetaEulerReciprocalAllowance.neg_log_norm_zeta_le hs).trans
  have hpos : 0 < (center x t + z).re - 1 := by linarith
  apply Real.log_le_log (by positivity)
  exact add_le_add_right (one_div_le_one_div_of_le hx hden) 1

theorem logDeriv_eq_boundary_moment_add_sum (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    logDeriv riemannZeta (center x t) = moment (translated x t) r + coupledSum x t r := by
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  have h := logDeriv_eq_moment_add_divisor hr hf hzero hs
  rwa [logDeriv_translated k (by omega) ht hx hx'] at h

theorem boundary_moment_le (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-moment (translated x t) r).re ≤ 2 * allowance k x t / (Real.pi * r) := by
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  apply AnalyticDiscSignedBoundary.neg_moment_re_le hr
    (hf.continuousOn.mono sphere_subset_closedBall)
    (fun z hz ↦ hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
  · intro z hz _
    have hn := ZetaNearOneFullDisc.norm_translated_le k hk ht hx hx'
      (closedBall_subset_closedBall hrδ (sphere_subset_closedBall hz))
    have hpos : 0 < ‖translated x t z‖ := norm_pos_iff.mpr
      (hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
    simpa only [Real.log_exp] using Real.log_le_log hpos hn
  · intro z _ hz
    exact right_arc_lower t hx hz

end
end RiemannGaussian.ZetaNearOneAngularBound
