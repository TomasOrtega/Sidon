/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.LogLogDerivativeSchedule
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneBudgetLimit

namespace RiemannGaussian.ZetaLogLogScale
noncomputable section
open Filter RiemannGaussian.ZetaNearOneBudgetLimit RiemannGaussian.ZetaNearOneLogProfile RiemannGaussian.DerivativeOrderComparison
open scoped Topology

def level (t : ℝ) : ℝ := Real.log (scale t)

def order (b t : ℝ) : ℕ := LogLogDerivativeSchedule.index b (scale t)

def width (C t : ℝ) : ℝ := C * level t / scale t

theorem level_atTop : Tendsto level atTop atTop :=
  Real.tendsto_log_atTop.comp scale_atTop

theorem order_atTop {b : ℝ} (hb : 0 < b) : Tendsto (order b) atTop atTop :=
  (LogLogDerivativeSchedule.index_atTop hb).comp scale_atTop

theorem level_div_order {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ ↦ level t / ((order b t : ℝ) + 2)) atTop (𝓝 b) :=
  (LogLogDerivativeSchedule.log_div_index hb).comp scale_atTop

theorem width_pos {C t : ℝ} (hC : 0 < C) (ht : 0 < level t) : 0 < width C t :=
  div_pos (mul_pos hC ht) (scale_pos t)

theorem width_tendsto_zero (C : ℝ) : Tendsto (width C) atTop (𝓝 0) := by
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp scale_atTop).const_mul C
  simp only [Function.comp_def, id_eq, mul_zero] at h
  convert h using 1
  funext t
  unfold width level
  ring

theorem pow_level_div_width_tendsto {b : ℝ} (hb : Real.log 2 < b) (n : ℕ) :
    Tendsto (fun t : ℝ ↦ level t ^ n / (scale t * delta (order b t)))
      atTop (𝓝 0) :=
  (LogLogDerivativeSchedule.pow_log_div_width_tendsto hb n).comp scale_atTop

theorem width_div_delta_tendsto {b : ℝ} (hb : Real.log 2 < b) (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t / delta (order b t)) atTop (𝓝 0) := by
  have h := (pow_level_div_width_tendsto hb 1).const_mul C
  simp only [pow_one, mul_zero] at h
  convert h using 1
  funext t
  unfold width
  ring

theorem width_mul_level_div_delta_tendsto {b : ℝ} (hb : Real.log 2 < b) (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t * level t / delta (order b t)) atTop (𝓝 0) := by
  have h := (pow_level_div_width_tendsto hb 2).const_mul C
  simp only [mul_zero] at h
  convert h using 1
  funext t
  unfold width
  ring

end
end RiemannGaussian.ZetaLogLogScale
