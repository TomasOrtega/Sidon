module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerReciprocalAllowance
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

@[expose] public section

namespace RiemannGaussian.ZetaNearOneJensen
noncomputable section
open Complex Metric Set MeromorphicOn RiemannGaussian.ZetaNearOneLocalDisc RiemannGaussian.ZetaNearOneLogProfile
open RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison RiemannGaussian.ZetaEulerReciprocalAllowance
def allowance (k : ℕ) (x t : ℝ) : ℝ :=
  profile k t + 14 + Real.log (1 + 1 / x)

theorem center_ne_zero (t : ℝ) {x : ℝ} (hx : 0 < x) : riemannZeta (center x t) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [ZetaNearOneLocalDisc.center, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  linarith

theorem center_log_bound (t : ℝ) {x : ℝ} (hx : 0 < x) :
    -Real.log ‖riemannZeta (center x t)‖ ≤ Real.log (1 + 1 / x) := by
  have hre : (center x t).re = 1 + x := by simp [ZetaNearOneLocalDisc.center]
  have h := neg_log_norm_zeta_le (s := center x t) (by rw [hre]; linarith)
  simpa only [hre, add_sub_cancel_left] using h

end
end RiemannGaussian.ZetaNearOneJensen
