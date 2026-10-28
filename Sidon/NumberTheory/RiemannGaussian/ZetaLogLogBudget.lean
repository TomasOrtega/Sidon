module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.ZetaAngularPrimeBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
public import Sidon.NumberTheory.RiemannGaussian.ZetaLogLogCorrection
public import Sidon.NumberTheory.RiemannGaussian.ZetaLogLogScale
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneBudgetLimit
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneJensen
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile

@[expose] public section

namespace RiemannGaussian.ZetaLogLogBudget
noncomputable section
open Filter RiemannGaussian.ZetaLogLogScale RiemannGaussian.ZetaLogLogCorrection RiemannGaussian.ZetaNearOneBudgetLimit
open RiemannGaussian.ZetaAngularPrimeBudget RiemannGaussian.ZetaNearOneJensen RiemannGaussian.ZetaNearOneLogProfile
open RiemannGaussian.DerivativeOrderComparison RiemannGaussian.DerivativePowerExponents
open scoped Topology

theorem scale_double_bounds (t : ℝ) :
    scale t ≤ scale (2 * t) ∧ scale (2 * t) ≤ 2 * scale t := by
  have hl : Real.log 2 ≤ scale t := Real.log_le_log (by norm_num) (two_le_height t)
  have hlo : height t ≤ height (2 * t) := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hhi : height (2 * t) ≤ 2 * height t := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h := Real.log_le_log (by linarith [two_le_height (2 * t)] : 0 < height (2 * t)) hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by linarith [two_le_height t] : height t ≠ 0)] at h
  refine ⟨Real.log_le_log (by linarith [two_le_height t]) hlo, ?_⟩
  change scale (2 * t) ≤ Real.log 2 + scale t at h
  linarith

theorem leading_identity (b C t v : ℝ) :
    width C t * (alpha (order b t) * scale v) / delta (order b t) =
      C * (level t / ((order b t : ℝ) + 2)) * (scale v / scale t) := by
  have ha := alpha_pos (order b t)
  unfold width delta
  field_simp

theorem normalized_allowance_tendsto {b C D q : ℝ}
    (hb : Real.log 2 < b) (hC : 0 < C) (hD : 0 < D) (v : ℝ → ℝ)
    (hv : ∀ᶠ t : ℝ in atTop, 0 ≤ level (v t) ∧ scale (v t) ≤ D * scale t)
    (hratio : Tendsto (fun t : ℝ ↦ scale (v t) / scale t) atTop (𝓝 q)) :
    Tendsto (fun t : ℝ ↦ width C t * allowance (order b t) (6 * width C t) (v t) /
      delta (order b t)) atTop (𝓝 (C * b * q)) := by
  have hbpos : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hmain := ((level_div_order hbpos).const_mul C).mul hratio
  have herr := normalized_correction_tendsto hb hC hD v hv
  have h := hmain.add herr
  simp only [add_zero] at h
  convert h using 1
  funext t
  rw [allowance_eq, ← leading_identity]
  ring

theorem width_mul_budget_tendsto {b C : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ width C t * budget (order b t) (6 * width C t) t)
      atTop (𝓝 (10 * C * b / Real.pi)) := by
  have hsame : ∀ᶠ t : ℝ in atTop, 0 ≤ level t ∧ scale t ≤ 1 * scale t := by
    filter_upwards [level_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with t ht
    exact ⟨ht, by simp⟩
  have hratio : Tendsto (fun t : ℝ ↦ scale t / scale t) atTop (𝓝 1) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)) using 1
    funext t
    exact div_self (scale_pos t).ne'
  have h1 := normalized_allowance_tendsto hb hC (by norm_num : (0 : ℝ) < 1)
    (fun t ↦ t) hsame hratio
  have hdouble : ∀ᶠ t : ℝ in atTop, 0 ≤ level (2 * t) ∧ scale (2 * t) ≤ 2 * scale t := by
    filter_upwards [level_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with t ht
    have hl := Real.log_le_log (scale_pos t) (scale_double_bounds t).1
    exact ⟨ht.trans hl, (scale_double_bounds t).2⟩
  have h2 := normalized_allowance_tendsto hb hC (by norm_num : (0 : ℝ) < 2)
    (fun t ↦ 2 * t) hdouble scale_double_div
  simp only [mul_one] at h1 h2
  have h := ((width_tendsto_zero C).const_mul (1344 * localZetaLogHeight 0)).add
    (((h1.const_mul 8).add (h2.const_mul 2)).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  have he : 8 * (C * b) + 2 * (C * b) = 10 * C * b := by ring
  rw [he] at h
  convert h using 1
  funext t
  unfold budget
  ring

end
end RiemannGaussian.ZetaLogLogBudget
