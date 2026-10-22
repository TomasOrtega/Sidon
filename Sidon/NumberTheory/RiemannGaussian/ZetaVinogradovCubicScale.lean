/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovHeightSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaledSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneBudgetLimit
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovBalancedScale
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovScheduledMargin

namespace RiemannGaussian.ZetaVinogradovCubicScale
noncomputable section
open Filter RiemannGaussian.VinogradovCubicBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovSharperBudget (delta delta_pos)
open RiemannGaussian.VinogradovHeightSchedule (size size_atTop balanced_identity)
open RiemannGaussian.ZetaNearOneBudgetLimit (scale scale_pos scale_atTop)
open RiemannGaussian.ZetaVinogradovBalancedScale (level width level_atTop)
open scoped Topology

def order (t : ℝ) : ℕ := VinogradovScaledSchedule.degree (scale t)

theorem order_atTop : Tendsto order atTop atTop := VinogradovScaledSchedule.degree_atTop.comp scale_atTop

theorem radius_scaled :
    Tendsto (fun t : ℝ ↦ delta (order t) * size (scale t) ^ 2) atTop (𝓝 (1 / 4)) :=
  VinogradovCubicSchedule.radius_scaled.comp scale_atTop

theorem growth_normalized :
    Tendsto (fun t : ℝ ↦ growth (order t) * scale t / level t) atTop (𝓝 5) :=
  VinogradovCubicSchedule.growth_normalized.comp scale_atTop

theorem width_mul_level_div_delta (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t * level t / delta (order t)) atTop (𝓝 (4 * C)) := by
  have h := (tendsto_const_nhds (x := C)).div radius_scaled
    (by norm_num : (1 / 4 : ℝ) ≠ 0)
  rw [show C / (1 / 4 : ℝ) = 4 * C by ring] at h
  apply h.congr'
  filter_upwards [scale_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with t ht
  have hl : 0 < level t := Real.log_pos ht
  have hs : 0 < size (scale t) := by
    unfold size
    exact Real.rpow_pos_of_pos (div_pos (scale_pos t) (Real.log_pos ht)) _
  have he := balanced_identity ht
  change size (scale t) ^ 2 * level t = scale t ^ (2 / 3 : ℝ) * level t ^ (1 / 3 : ℝ) at he
  simp only [Pi.div_apply, width]
  rw [← he]
  field_simp

theorem width_div_delta_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t / delta (order t)) atTop (𝓝 0) := by
  have h := (width_mul_level_div_delta C).div_atTop level_atTop
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  field_simp

theorem eventually_parameters : ∀ᶠ t : ℝ in atTop,
    48 ≤ order t ∧ (heightThreshold (8 * order t) : ℝ) + 1 ≤ t := by
  filter_upwards [ZetaVinogradovScheduledMargin.eventually_parameters,
    order_atTop.eventually (eventually_ge_atTop 48),
    (size_atTop.comp scale_atTop).eventually (eventually_ge_atTop (0 : ℝ))] with t ht hn hs
  refine ⟨hn, ?_⟩
  have h : (heightThreshold (8 * order t) : ℝ) ≤
      heightThreshold (ZetaVinogradovScheduledMargin.order t) := by
    exact_mod_cast VinogradovScaledSchedule.heightThreshold_mono
      (VinogradovCubicSchedule.eight_degree_le_index hs)
  linarith [ht.2.1]

theorem abs_invariance (C t : ℝ) :
    order |t| = order t ∧ level |t| = level t ∧ width C |t| = width C t := by
  simp [order, level, width, scale, ZetaNearOneLogProfile.height]

end
end RiemannGaussian.ZetaVinogradovCubicScale
