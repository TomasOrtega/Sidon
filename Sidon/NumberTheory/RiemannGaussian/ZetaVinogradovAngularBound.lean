module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscBoundaryMoment
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscBoundarySequence
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscSignedBoundary
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneAngularBound
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneJensen
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneSignedBound
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCanonical
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovFullDisc

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovAngularBound
noncomputable section
open Complex Filter Metric Set MeromorphicOn RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.ZetaVinogradovLocalDisc RiemannGaussian.ZetaVinogradovCanonical
open RiemannGaussian.ZetaNearOneLocalDisc (center)
open RiemannGaussian.ZetaNearOneCanonical (translated translated_zero)
open RiemannGaussian.ZetaNearOneJensen (center_ne_zero)
open RiemannGaussian.ZetaNearOneSignedBound (coupledSum coupledSum_nonneg source_le_sum)
open RiemannGaussian.AnalyticDiscBoundaryMoment
open scoped Topology

theorem logDeriv_eq_boundary_moment_add_sum (k : ℕ) (hk : 12 ≤ k) {t x r : ℝ}
    (ht : (heightThreshold k : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    logDeriv riemannZeta (center x t) = moment (translated x t) r + coupledSum x t r := by
  have hf := (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  have h := logDeriv_eq_moment_add_divisor hr hf hzero hs
  rwa [logDeriv_translated k (by omega) ht hx hx'] at h

theorem boundary_moment_le (k : ℕ) (hk : 12 ≤ k) {t x r : ℝ}
    (ht : (heightThreshold k : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-moment (translated x t) r).re ≤ 2 * allowance k x t / (Real.pi * r) := by
  have hf := (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  apply AnalyticDiscSignedBoundary.neg_moment_re_le hr
    (hf.continuousOn.mono sphere_subset_closedBall)
    (fun z hz ↦ hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
  · intro z hz _
    have hn := ZetaVinogradovFullDisc.norm_translated_le k hk ht hx hx'
      (closedBall_subset_closedBall hrδ (sphere_subset_closedBall hz))
    have hpos : 0 < ‖translated x t z‖ := norm_pos_iff.mpr
      (hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
    simpa only [Real.log_exp] using Real.log_le_log hpos hn
  · intro z _ hz
    exact ZetaNearOneAngularBound.right_arc_lower t hx hz

theorem neg_logDeriv_re_le_at_radius (k : ℕ) (hk : 12 ≤ k) {t x r : ℝ}
    (ht : (heightThreshold k : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / (Real.pi * r) := by
  have hb := boundary_moment_le k hk ht hx hx' hr hrδ hs
  have hf := (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsum := coupledSum_nonneg hx hr hf
  rw [logDeriv_eq_boundary_moment_add_sum k hk ht hx hx' hr hrδ hs, neg_add, Complex.add_re,
    Complex.neg_re]
  simp only [Complex.neg_re] at hb ⊢
  linarith

theorem neg_logDeriv_re_le_sub_zero_at_radius (k : ℕ) (hk : 12 ≤ k)
    (ρ : NontrivialZetaZero) {x r : ℝ} (ht : (heightThreshold k : ℝ) + 1 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r) (hrδ : r ≤ delta k)
    (hs : ∀ z : ℂ, ‖z‖ = r → translated x ρ.1.im z ≠ 0)
    (hnear : x + 1 - ρ.1.re < r) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * allowance k x ρ.1.im / (Real.pi * r) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / r ^ 2) := by
  have hb := boundary_moment_le k hk ht hx hx' hr hrδ hs
  have hf := (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsource := source_le_sum ρ hx hr hf hnear
  rw [logDeriv_eq_boundary_moment_add_sum k hk ht hx hx' hr hrδ hs, neg_add, Complex.add_re,
    Complex.neg_re]
  simp only [Complex.neg_re] at hb ⊢
  linarith

theorem neg_logDeriv_re_le (k : ℕ) (hk : 12 ≤ k) {t x : ℝ}
    (ht : (heightThreshold k : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / (Real.pi * delta k) := by
  have hδ := delta_pos k
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x t / (Real.pi * r n)) atTop
      (𝓝 (2 * allowance k x t / (Real.pi * delta k))) :=
    tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hδ).ne'
  exact ge_of_tendsto' hl (fun n ↦ neg_logDeriv_re_le_at_radius k hk ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2)

theorem neg_logDeriv_re_le_sub_zero (k : ℕ) (hk : 12 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : (heightThreshold k : ℝ) + 1 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * allowance k x ρ.1.im / (Real.pi * delta k) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2) := by
  have hδ := delta_pos k
  have hzero : translated x ρ.1.im 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero ρ.1.im hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaVinogradovFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x ρ.1.im / (Real.pi * r n) -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (r n) ^ 2)) atTop
      (𝓝 (2 * allowance k x ρ.1.im / (Real.pi * delta k) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2))) :=
    (tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hδ).ne').sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.div (hlim.pow 2)
        (pow_ne_zero 2 hδ.ne'))).const_mul _)
  apply ge_of_tendsto hl
  filter_upwards [hlim.eventually (lt_mem_nhds hnear)] with n hn
  exact neg_logDeriv_re_le_sub_zero_at_radius k hk ρ ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2 hn

end
end RiemannGaussian.ZetaVinogradovAngularBound
