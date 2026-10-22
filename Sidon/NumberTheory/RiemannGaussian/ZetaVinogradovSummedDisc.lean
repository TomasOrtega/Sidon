/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCubicDisc
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovSummedBound

namespace RiemannGaussian.ZetaVinogradovSummedDisc
noncomputable section
open Complex Metric Set RiemannGaussian.VinogradovCubicBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovSharperBudget (delta line)
open RiemannGaussian.ZetaNearOneLogProfile (height two_le_height)
open RiemannGaussian.ZetaNearOneLocalDisc (center)
open RiemannGaussian.ZetaNearOneCanonical (translated)
def profile (n : ℕ) (t : ℝ) : ℝ :=
  Real.log 1048576 + growth n * Real.log (height t) +
    (2 / 3) * Real.log (Real.log (height t))

theorem profile_eq_log (n : ℕ) (t : ℝ) :
    profile n t = Real.log
      (1048576 * height t ^ growth n * (Real.log (height t)) ^ (2 / 3 : ℝ)) := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 1048576)
    (Real.rpow_pos_of_pos hh _)).ne' (Real.rpow_pos_of_pos hl _).ne',
    Real.log_mul (by norm_num : (1048576 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hh _).ne',
    Real.log_rpow hh, Real.log_rpow hl]
  rfl

theorem local_norm_bound (n : ℕ) (hn : 48 ≤ n) {t : ℝ}
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |t|) {s : ℂ}
    (hlo : line n ≤ s.re) (hhi : s.re ≤ 3 / 2) (hw : |s.im - t| ≤ 1) :
    ‖riemannZeta s‖ ≤ Real.exp (profile n t) := by
  have hreverse : |t| ≤ |s.im| + |s.im - t| := by
    calc
      |t| = |s.im + (t - s.im)| := by congr 1; ring
      _ ≤ |s.im| + |t - s.im| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm t s.im]
  have ht' : (heightThreshold (8 * n) : ℝ) ≤ |s.im| := by linarith
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
  have hpos : 0 < |s.im| := by linarith
  have hupper : |s.im| ≤ height t := by
    have h := abs_add_le (s.im - t) t
    rw [sub_add_cancel] at h
    unfold height
    linarith
  have hp := Real.rpow_le_rpow (abs_nonneg s.im) hupper (growth_pos n).le
  have hl := Real.rpow_le_rpow (Real.log_nonneg (by linarith : 1 ≤ |s.im|))
    (Real.log_le_log hpos hupper) (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hm := mul_le_mul hp hl (Real.rpow_nonneg (Real.log_nonneg (by linarith : 1 ≤ |s.im|)) _)
    (Real.rpow_nonneg (by linarith [two_le_height t] : 0 ≤ height t) _)
  rw [profile_eq_log, Real.exp_log (by
    have hH : 0 < height t := by linarith [two_le_height t]
    have hlH : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
    positivity)]
  apply (ZetaVinogradovSummedBound.bound_strip_abs n hn hlo hhi ht').trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1048576)

theorem norm_translated_le (n : ℕ) (hn : 48 ≤ n) {t x : ℝ}
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta n)) :
    ‖translated x t z‖ ≤ Real.exp (profile n t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, hw⟩ := ZetaVinogradovCubicDisc.disc_geometry n t hx hx' hm
  exact local_norm_bound n hn ht hlo hhi hw

end
end RiemannGaussian.ZetaVinogradovSummedDisc
