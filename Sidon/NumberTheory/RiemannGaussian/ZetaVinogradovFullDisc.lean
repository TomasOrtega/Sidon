module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovLocalDisc

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovFullDisc
noncomputable section
open Complex Metric Set RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.ZetaVinogradovLocalDisc
open RiemannGaussian.ZetaNearOneLocalDisc (center)
open RiemannGaussian.ZetaNearOneCanonical (translated)
theorem disc_geometry (n : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {s : ℂ} (hs : s ∈ closedBall (center x t) (delta n)) :
    line n ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta n := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ := delta_le n
  refine ⟨?_, ?_, ?_⟩
  · unfold line
    linarith [(abs_le.mp hre).1]
  · linarith [(abs_le.mp hre).2]
  · linarith

theorem analyticOnNhd_translated (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta n)) := by
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have ha := analyticOn_riemannZeta (z + center x t)
    (ZetaNearOneLocalDisc.ne_one_of_window (by linarith) (disc_geometry n t hx hx' hm).2.2)
  exact ha.comp (f := fun w : ℂ ↦ w + center x t) (by fun_prop)

theorem norm_translated_le (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta n)) :
    ‖translated x t z‖ ≤ Real.exp (profile n t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, hw⟩ := disc_geometry n t hx hx' hm
  exact local_norm_bound n hn ht hlo hhi hw

end
end RiemannGaussian.ZetaVinogradovFullDisc
