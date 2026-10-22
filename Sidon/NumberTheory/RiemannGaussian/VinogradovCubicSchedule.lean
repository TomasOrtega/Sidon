/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovHeightSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaledSchedule
import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget

namespace RiemannGaussian.VinogradovCubicSchedule
noncomputable section
open Filter RiemannGaussian.VinogradovCubicBudget RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovSharperBudget (delta)
open RiemannGaussian.VinogradovHeightSchedule (size size_atTop size_cube)
open RiemannGaussian.VinogradovScaledSchedule (degree degree_atTop affine_ratio heightThreshold_mono)
open scoped Topology

theorem radius_scaled :
    Tendsto (fun L : ℝ ↦ delta (degree L) * size L ^ 2) atTop (𝓝 (1 / 4)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div ((affine_ratio.pow 2).const_mul 4096)
    (by norm_num : (4096 : ℝ) * (1 / 32) ^ 2 ≠ 0)
  rw [show (1 : ℝ) / (4096 * (1 / 32) ^ 2) = 1 / 4 by norm_num] at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL
  simp only [Pi.div_apply]
  unfold delta
  field_simp

theorem growth_scaled :
    Tendsto (fun L : ℝ ↦ growth (degree L) * size L ^ 3) atTop (𝓝 5) := by
  have h := (tendsto_const_nhds (x := (5 : ℝ))).div ((affine_ratio.pow 3).const_mul 32768)
    (by norm_num : (32768 : ℝ) * (1 / 32) ^ 3 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL
  simp only [Pi.div_apply, growth_eq]
  field_simp

theorem growth_normalized :
    Tendsto (fun L : ℝ ↦ growth (degree L) * L / Real.log L) atTop (𝓝 5) := by
  apply growth_scaled.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [size_cube hL]
  ring

theorem eight_degree_le_index {L : ℝ} (hs : 0 ≤ size L) :
    8 * degree L ≤ VinogradovHeightSchedule.index L := by
  unfold VinogradovHeightSchedule.index
  apply (Nat.le_floor_iff hs).mpr
  have hf := Nat.floor_le (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 64))
  change (degree L : ℝ) ≤ size L / 64 at hf
  push_cast
  linarith

end
end RiemannGaussian.VinogradovCubicSchedule
