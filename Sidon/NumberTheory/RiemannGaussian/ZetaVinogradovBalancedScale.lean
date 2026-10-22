/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovHeightSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaledSchedule
import Sidon.NumberTheory.RiemannGaussian.ZetaLogLogScale
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneBudgetLimit
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovScheduledMargin

namespace RiemannGaussian.ZetaVinogradovBalancedScale
noncomputable section
open Filter RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovHeightSchedule (size size_atTop balanced_identity)
open RiemannGaussian.ZetaNearOneBudgetLimit (scale scale_pos scale_atTop scale_double_div)
open scoped Topology

def order (t : ℝ) : ℕ := VinogradovScaledSchedule.degree (scale t)

def level (t : ℝ) : ℝ := Real.log (scale t)

def width (C t : ℝ) : ℝ := C / (scale t ^ (2 / 3 : ℝ) * level t ^ (1 / 3 : ℝ))

theorem level_atTop : Tendsto level atTop atTop := Real.tendsto_log_atTop.comp scale_atTop

theorem order_atTop : Tendsto order atTop atTop := VinogradovScaledSchedule.degree_atTop.comp scale_atTop

theorem radius_scaled :
    Tendsto (fun t : ℝ ↦ delta (order t) * size (scale t) ^ 2) atTop (𝓝 (1 / 64)) :=
  VinogradovScaledSchedule.radius_scaled.comp scale_atTop

theorem growth_normalized :
    Tendsto (fun t : ℝ ↦ growth (order t) * scale t / level t) atTop (𝓝 2) :=
  VinogradovScaledSchedule.growth_normalized.comp scale_atTop

theorem level_double_ratio :
    Tendsto (fun t : ℝ ↦ level (2 * t) / level t) atTop (𝓝 1) := by
  have hlog := scale_double_div.log (by norm_num : (1 : ℝ) ≠ 0)
  have h := (hlog.div_atTop level_atTop).const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  rw [Real.log_div (scale_pos (2 * t)).ne' (scale_pos t).ne']
  change 1 + (level (2 * t) - level t) / level t = _
  field_simp
  ring

theorem width_pos {C t : ℝ} (hC : 0 < C) (ht : 0 < level t) : 0 < width C t := by
  unfold width
  positivity [scale_pos t]

theorem width_tendsto_zero (C : ℝ) : Tendsto (width C) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp scale_atTop
  have h₂ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp level_atTop
  exact (h₁.atTop_mul_atTop₀ h₂).const_div_atTop C

theorem width_mul_level_div_delta (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t * level t / delta (order t)) atTop (𝓝 (64 * C)) := by
  have h := (tendsto_const_nhds (x := C)).div radius_scaled
    (by norm_num : (1 / 64 : ℝ) ≠ 0)
  rw [show C / (1 / 64 : ℝ) = 64 * C by ring] at h
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

theorem log_width_ratio {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ Real.log (width C t) / level t) atTop (𝓝 (-(2 / 3 : ℝ))) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp level_atTop
  have h := ((level_atTop.const_div_atTop (Real.log C)).sub
    (tendsto_const_nhds (x := (2 / 3 : ℝ)))).sub (hsmall.const_mul (1 / 3 : ℝ))
  simp only [mul_zero, sub_zero, zero_sub] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hL := scale_pos t
  simp only [Function.comp_def, id_eq, width]
  rw [Real.log_div hC.ne' (by positivity : scale t ^ (2 / 3 : ℝ) * level t ^ (1 / 3 : ℝ) ≠ 0),
    Real.log_mul (Real.rpow_pos_of_pos hL _).ne' (Real.rpow_pos_of_pos ht _).ne',
    Real.log_rpow hL, Real.log_rpow ht]
  change Real.log C / level t - 2 / 3 - (1 / 3) * (Real.log (level t) / level t) =
    (Real.log C - ((2 / 3) * level t + (1 / 3) * Real.log (level t))) / level t
  field_simp
  ring

theorem eventually_parameters : ∀ᶠ t : ℝ in atTop,
    12 ≤ order t ∧ (heightThreshold (order t) : ℝ) + 1 ≤ t := by
  filter_upwards [ZetaVinogradovScheduledMargin.eventually_parameters,
    order_atTop.eventually (eventually_ge_atTop 12),
    (size_atTop.comp scale_atTop).eventually (eventually_ge_atTop (0 : ℝ))] with t ht hn hs
  refine ⟨hn, ?_⟩
  have h : (heightThreshold (order t) : ℝ) ≤
      heightThreshold (ZetaVinogradovScheduledMargin.order t) := by
    exact_mod_cast VinogradovScaledSchedule.heightThreshold_mono
      (VinogradovScaledSchedule.degree_le_index hs)
  linarith [ht.2.1]

theorem abs_invariance (C t : ℝ) :
    order |t| = order t ∧ level |t| = level t ∧ width C |t| = width C t := by
  simp [order, level, width, scale, ZetaNearOneLogProfile.height]

end
end RiemannGaussian.ZetaVinogradovBalancedScale
