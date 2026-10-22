/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer
import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianStrip
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

namespace RiemannGaussian.ZetaNearOneLocalDisc
noncomputable section
open Complex Metric Set RiemannGaussian.ZetaGaussianLocalizer RiemannGaussian.ZetaGaussianStrip
open RiemannGaussian.ZetaNearOneLogProfile RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
theorem reconstruction (t : ℝ) {s : ℂ} (hs : s ≠ 1) (hs' : s + 1 ≠ 0) :
    riemannZeta s = carrier t s * Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2)) *
      ((s + 1) / (s - 1)) := by
  have hcancel : carrier t s * Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2)) =
      regularized s := by
    rw [carrier, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hcancel, regularized_eq hs]
  field_simp [hs', sub_ne_zero.mpr hs]

theorem inverse_gaussian_bound (t : ℝ) {s : ℂ} (h : |s.im - t| ≤ 1) :
    ‖Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2))‖ ≤ Real.exp 1 := by
  have he : ((s - Complex.I * (t : ℂ)) ^ 2).re = s.re ^ 2 - (s.im - t) ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, sub_zero, zero_add]
  rw [Complex.norm_exp, Complex.neg_re, he]
  apply Real.exp_le_exp.mpr
  have hsq : (s.im - t) ^ 2 ≤ 1 := by
    have h' := (sq_le_sq₀ (abs_nonneg (s.im - t)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
    simpa only [sq_abs, one_pow] using h'
  nlinarith [sq_nonneg s.re]

theorem inverse_ratio_bound {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hy : 1 ≤ |s.im|) : ‖(s + 1) / (s - 1)‖ ≤ 4 := by
  have hden : |s.im| ≤ ‖s - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1)
  have hnum := Complex.norm_le_abs_re_add_abs_im (s + 1)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hnum
  rw [abs_of_nonneg (by linarith : 0 ≤ s.re + 1)] at hnum
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
  linarith

theorem one_le_abs_im {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ} (hs : |s.im - t| ≤ 1) :
    1 ≤ |s.im| := by
  have h : |t| ≤ |s.im| + |s.im - t| := by
    calc
      |t| = |s.im + (t - s.im)| := by congr 1; ring
      _ ≤ |s.im| + |t - s.im| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm t s.im]
  linarith

theorem ne_one_of_window {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ} (hs : |s.im - t| ≤ 1) :
    s ≠ 1 := by
  have h := one_le_abs_im ht hs
  intro he
  norm_num [he] at h

theorem local_norm_bound (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) (hwindow : |s.im - t| ≤ 1) :
    ‖riemannZeta s‖ ≤ Real.exp (profile k t + 14) := by
  have hs : 1 / 2 ≤ s.re := (half_le_line k hk).trans hlo
  rw [reconstruction t (ne_one_of_window ht hwindow) (add_one_ne_zero (by linarith)),
    norm_mul, norm_mul]
  have hm := mul_le_mul
    (mul_le_mul (carrier_bound k hk t hlo hhi) (inverse_gaussian_bound t hwindow)
      (norm_nonneg _) (Real.exp_pos _).le)
    (inverse_ratio_bound hs hhi (one_le_abs_im ht hwindow)) (norm_nonneg _)
    (by positivity)
  apply hm.trans
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    Real.exp (profile k t + 10) * Real.exp 1 * 4 ≤
        Real.exp (profile k t + 10) * Real.exp 1 * Real.exp 3 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.exp (profile k t + 14) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

def center (x t : ℝ) : ℂ := ((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ)

theorem disc_geometry (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {x : ℝ}
    (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k / 2)) :
    line k ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta k / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ : delta k ≤ 1 / 2 := by
    rw [delta_eq_one_sub_line]
    linarith [half_le_line k hk]
  have hline : line k = 1 - delta k := by rw [delta_eq_one_sub_line]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hline]
    linarith [(abs_le.mp hre).1, delta_pos k]
  · linarith [(abs_le.mp hre).2]
  · linarith

theorem analyticOnNhd_disc (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (center x t) (delta k / 2)) := by
  intro s hs
  exact analyticOn_riemannZeta s (ne_one_of_window ht (disc_geometry k hk t hx hx' hs).2.2)

end
end RiemannGaussian.ZetaNearOneLocalDisc
