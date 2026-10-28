module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic
public import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents

@[expose] public section

namespace RiemannGaussian.LogLogDerivativeSchedule
noncomputable section
open Filter RiemannGaussian.DerivativeOrderComparison RiemannGaussian.DerivativePowerExponents
open scoped Topology

def index (b L : ℝ) : ℕ := ⌊Real.log L / b⌋₊

def exponent (b : ℝ) : ℝ := Real.log 2 / b

theorem index_atTop {b : ℝ} (hb : 0 < b) : Tendsto (index b) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const hb)

theorem index_div_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ ↦ ((index b L : ℝ) + 2) / Real.log L) atTop (𝓝 (1 / b)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ 1 / b by positivity)).comp
    Real.tendsto_log_atTop
  have hc := Real.tendsto_log_atTop.const_div_atTop (2 : ℝ)
  have hh := h.add hc
  simp only [add_zero] at hh
  convert hh using 1
  funext L
  simp only [Function.comp_def, index, one_div_mul_eq_div, add_div]

theorem log_div_index {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ ↦ Real.log L / ((index b L : ℝ) + 2)) atTop (𝓝 b) := by
  simpa only [inv_div, div_one] using
    (index_div_log hb).inv₀ (by positivity : (1 : ℝ) / b ≠ 0)

theorem exponent_lt_one {b : ℝ} (hb : Real.log 2 < b) : exponent b < 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_lt_one (by linarith : 0 < b)).mpr hb

theorem delta_le_one (k : ℕ) : delta k ≤ 1 := by
  have h := delta_antitone (Nat.zero_le k)
  norm_num [delta, alpha] at h ⊢
  exact h

theorem inverse_delta_le_power (k : ℕ) : 1 / delta k ≤ (2 : ℝ) ^ (k + 2) := by
  have hd := delta_pos k
  have hden := denominator_ge_two k
  have hmul : 1 ≤ (2 : ℝ) ^ (k + 2) * delta k := by
    unfold delta alpha
    rw [mul_one_div, ← mul_div_assoc]
    apply (le_div_iff₀ (by linarith : 0 < (2 : ℝ) ^ (k + 2) - 2)).mpr
    have hp : 0 ≤ (k : ℝ) * (2 : ℝ) ^ (k + 2) := by positivity
    nlinarith
  exact (div_le_iff₀ hd).mpr hmul

theorem power_index_le {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    (2 : ℝ) ^ (index b L + 2) ≤ 4 * L ^ exponent b := by
  have hLp : 0 < L := by linarith
  have hf : (index b L : ℝ) ≤ Real.log L / b :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hL) hb.le)
  have hp : (2 : ℝ) ^ index b L ≤ L ^ exponent b := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    calc
      Real.log 2 * (index b L : ℝ) ≤ Real.log 2 * (Real.log L / b) :=
        mul_le_mul_of_nonneg_left hf (Real.log_nonneg (by norm_num))
      _ = Real.log L * exponent b := by unfold exponent; ring
  rw [pow_add]
  norm_num
  linarith

theorem inverse_delta_le {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    1 / delta (index b L) ≤ 4 * L ^ exponent b :=
  (inverse_delta_le_power _).trans (power_index_le hb hL)

theorem log_width_le {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    Real.log (32768 / delta (index b L)) ≤
      Real.log 131072 + exponent b * Real.log L := by
  have hLp : 0 < L := by linarith
  have hd := delta_pos (index b L)
  have hbnd : 32768 / delta (index b L) ≤ 131072 * L ^ exponent b := by
    calc
      32768 / delta (index b L) = 32768 * (1 / delta (index b L)) := by ring
      _ ≤ 32768 * (4 * L ^ exponent b) :=
        mul_le_mul_of_nonneg_left (inverse_delta_le hb hL) (by norm_num)
      _ = 131072 * L ^ exponent b := by ring
  have h := Real.log_le_log (by positivity : 0 < 32768 / delta (index b L)) hbnd
  rw [Real.log_mul (by norm_num : (131072 : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hLp _).ne', Real.log_rpow hLp] at h
  exact h

theorem pow_log_div_width_tendsto {b : ℝ} (hb : Real.log 2 < b) (n : ℕ) :
    Tendsto (fun L : ℝ ↦ (Real.log L) ^ n / (L * delta (index b L)))
      atTop (𝓝 0) := by
  have hbp : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hs : 0 < 1 - exponent b := sub_pos.mpr (exponent_lt_one hb)
  have hlim : Tendsto (fun L : ℝ ↦ 4 * ((Real.log L) ^ n / L ^ (1 - exponent b)))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      ((isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).tendsto_div_nhds_zero.const_mul 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact div_nonneg (pow_nonneg (Real.log_nonneg hL) _) (by positivity [delta_pos (index b L)])
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hLp : 0 < L := by linarith
    have hp : 0 ≤ (Real.log L) ^ n / L := by positivity [Real.log_nonneg hL]
    calc
      (Real.log L) ^ n / (L * delta (index b L)) =
          ((Real.log L) ^ n / L) * (1 / delta (index b L)) := by ring
      _ ≤ ((Real.log L) ^ n / L) * (4 * L ^ exponent b) :=
        mul_le_mul_of_nonneg_left (inverse_delta_le hbp hL) hp
      _ = 4 * ((Real.log L) ^ n / L ^ (1 - exponent b)) := by
        rw [Real.rpow_sub hLp, Real.rpow_one]
        field_simp

end
end RiemannGaussian.LogLogDerivativeSchedule
