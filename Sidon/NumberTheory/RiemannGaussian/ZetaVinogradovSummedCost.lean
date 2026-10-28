module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaAngularDiscBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneBudgetLimit
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovBalancedBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovBalancedScale
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCubicDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCubicScale
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovSummedDisc

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovSummedCost
noncomputable section
open Filter RiemannGaussian.VinogradovCubicBudget RiemannGaussian.VinogradovScaleSelection RiemannGaussian.ZetaVinogradovCubicScale
open RiemannGaussian.VinogradovSharperBudget (delta delta_pos delta_le)
open RiemannGaussian.ZetaVinogradovBalancedScale (width level level_atTop level_double_ratio width_tendsto_zero)
open RiemannGaussian.ZetaNearOneBudgetLimit (scale scale_pos scale_double_div)
open RiemannGaussian.ZetaVinogradovSummedDisc (profile)
open RiemannGaussian.ZetaVinogradovBalancedBudget (center_log_normalized)
open scoped Topology

def allowance (n : ℕ) (x t : ℝ) : ℝ := profile n t + Real.log (1 + 1 / x)

def budget (n : ℕ) (x t : ℝ) : ℝ :=
  ZetaAngularDiscBudget.budget (delta n) (profile n t) (profile n (2 * t)) x

theorem margin_of_budget (n : ℕ) (hn : 48 ≤ n) (ρ : NontrivialZetaZero)
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |ρ.1.im|) {d : ℝ} (hd : 0 < d)
    (hdsmall : d < delta n / 28)
    (hpay : 14 * d * budget n (6 * d) ρ.1.im + 392 * d ^ 2 / (delta n) ^ 2 < 1) :
    d < 1 - ρ.1.re := by
  have hx : 0 < 6 * d := by positivity
  have hx' : 6 * d ≤ delta n / 4 := by linarith
  have ht₂ : (heightThreshold (8 * n) : ℝ) + 1 ≤ |2 * ρ.1.im| := by
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg ρ.1.im]
  exact ZetaAngularDiscBudget.margin_of_budget ρ (delta_pos n)
    ((delta_le n).trans (by norm_num)) hd hdsmall
    (ZetaVinogradovCubicDisc.analyticOnNhd_translated n hn ht hx hx')
    (fun _ hz ↦ ZetaVinogradovSummedDisc.norm_translated_le n hn ht hx hx' hz)
    (ZetaVinogradovCubicDisc.analyticOnNhd_translated n hn ht₂ hx hx')
    (fun _ hz ↦ ZetaVinogradovSummedDisc.norm_translated_le n hn ht₂ hx hx' hz) hpay

def cost (C t : ℝ) : ℝ :=
  14 * width C t * budget (order t) (6 * width C t) t +
    392 * (width C t) ^ 2 / (delta (order t)) ^ 2

theorem profile_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) t / level t) atTop (𝓝 (17 / 3 : ℝ)) := by
  have h := ((level_atTop.const_div_atTop (Real.log 1048576)).add growth_normalized).add
    (tendsto_const_nhds (x := (2 / 3 : ℝ)))
  norm_num only [zero_add, show (5 : ℝ) + 2 / 3 = 17 / 3 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  change Real.log 1048576 / level t + growth (order t) * scale t / level t + 2 / 3 =
    (Real.log 1048576 + growth (order t) * scale t + (2 / 3) * level t) / level t
  field_simp

theorem profile_double_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) (2 * t) / level t) atTop (𝓝 (17 / 3 : ℝ)) := by
  have hg := growth_normalized.mul scale_double_div
  simp only [mul_one] at hg
  have h := ((level_atTop.const_div_atTop (Real.log 1048576)).add hg).add (level_double_ratio.const_mul (2 / 3 : ℝ))
  norm_num only [zero_add, show (5 : ℝ) + 2 / 3 = 17 / 3 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hL := scale_pos t
  change Real.log 1048576 / level t +
    (growth (order t) * scale t / level t) * (scale (2 * t) / scale t) +
      (2 / 3) * (level (2 * t) / level t) =
    (Real.log 1048576 + growth (order t) * scale (2 * t) + (2 / 3) * level (2 * t)) / level t
  field_simp

theorem allowance_normalized {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) t / level t)
      atTop (𝓝 (19 / 3 : ℝ)) ∧
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) (2 * t) / level t)
      atTop (𝓝 (19 / 3 : ℝ)) := by
  have h₁ := profile_normalized.add (center_log_normalized hC)
  have h₂ := profile_double_normalized.add (center_log_normalized hC)
  norm_num only [show (17 / 3 : ℝ) + 2 / 3 = 19 / 3 by norm_num] at h₁ h₂
  constructor
  · convert h₁ using 1
    funext t
    unfold allowance
    ring
  · convert h₂ using 1
    funext t
    unfold allowance
    ring

theorem width_mul_budget_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ width C t * budget (order t) (6 * width C t) t)
      atTop (𝓝 (760 * C / (3 * Real.pi))) := by
  obtain ⟨h₁, h₂⟩ := allowance_normalized hC
  have h := ((width_tendsto_zero C).const_mul (1344 * localZetaLogHeight 0)).add
    (((width_mul_level_div_delta C).mul ((h₁.const_mul 8).add (h₂.const_mul 2))).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  rw [show (4 * C) * (8 * (19 / 3 : ℝ) + 2 * (19 / 3)) / Real.pi =
    760 * C / (3 * Real.pi) by ring] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  unfold budget ZetaAngularDiscBudget.budget allowance
  field_simp

theorem cost_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (cost C) atTop (𝓝 (10640 * C / (3 * Real.pi))) := by
  have h := ((width_mul_budget_tendsto hC).const_mul 14).add
    (((width_div_delta_tendsto C).pow 2).const_mul 392)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h
  rw [show (14 : ℝ) * (760 * C / (3 * Real.pi)) = 10640 * C / (3 * Real.pi) by ring] at h
  convert h using 1
  funext t
  unfold cost
  ring

end
end RiemannGaussian.ZetaVinogradovSummedCost
