/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

namespace RiemannGaussian.ZetaNearOneFullDisc
noncomputable section
open Complex Metric Set RiemannGaussian.ZetaNearOneLocalDisc RiemannGaussian.ZetaNearOneLogProfile
open RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison RiemannGaussian.ZetaNearOneCanonical
theorem delta_le_two_sevenths {k : ℕ} (hk : 2 ≤ k) : delta k ≤ 2 / 7 := by
  have h := delta_antitone hk
  have htwo : delta 2 = 2 / 7 := by norm_num [delta, DerivativePowerExponents.alpha]
  exact h.trans_eq htwo

theorem disc_geometry (k : ℕ) (hk : 2 ≤ k) (t : ℝ) {x : ℝ}
    (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k)) :
    line k ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta k := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ := delta_le_two_sevenths hk
  have hline : line k = 1 - delta k := by rw [delta_eq_one_sub_line]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hline]
    linarith [(abs_le.mp hre).1]
  · linarith [(abs_le.mp hre).2]
  · linarith

theorem analyticOnNhd_translated (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta k)) := by
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta k) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have ha := analyticOn_riemannZeta (z + center x t)
    (ne_one_of_window ht (disc_geometry k hk t hx hx' hm).2.2)
  exact ha.comp (f := fun w : ℂ ↦ w + center x t)
    (show AnalyticAt ℂ (fun w : ℂ ↦ w + center x t) z by fun_prop)

theorem norm_translated_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta k)) :
    ‖translated x t z‖ ≤ Real.exp (profile k t + 14) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta k) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, him⟩ := disc_geometry k hk t hx hx' hm
  exact local_norm_bound k (by omega) ht hlo hhi him

end
end RiemannGaussian.ZetaNearOneFullDisc
