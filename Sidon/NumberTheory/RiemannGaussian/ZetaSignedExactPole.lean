module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalLogDerivative
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
public import Sidon.NumberTheory.RiemannGaussian.ZetaSignedLocalEstimate

@[expose] public section

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

theorem zetaPole_real_part (x y : ℝ) :
    (1 / ((x : ℂ) + I * y)).re = x / (x ^ 2 + y ^ 2) := by
  simp only [one_div, Complex.inv_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.normSq_apply, Complex.add_im, Complex.mul_im,
    Complex.I_im, one_mul, zero_add]
  ring

theorem neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (y : ℝ)
    {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      x / (x ^ 2 + y ^ 2) + 448 * localZetaLogHeight y -
        (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  have hnorm : ‖((x - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hrem := norm_localZetaLogRemainder_le y hnorm
  rw [neg_logDeriv_riemannZeta_eq_local y hx hxsmall, Complex.sub_re, Complex.sub_re, zetaPole_real_part]
  linarith [(abs_le.mp (Complex.abs_re_le_norm (localZetaLogRemainder y ((x - 1 / 2 : ℝ) : ℂ)))).1]

theorem neg_logDeriv_riemannZeta_real_le_local {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re ≤ 1 / x + 448 * localZetaLogHeight 0 := by
  have h := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum 0 hx hxsmall
  have hp := localZetaPoleSum_re_nonneg 0 hx
  have he : x / (x ^ 2 + (0 : ℝ) ^ 2) = 1 / x := by field_simp; ring
  simpa only [Complex.ofReal_zero, mul_zero, add_zero, he] using h.trans (sub_le_self _ hp)

end

end RiemannGaussian
