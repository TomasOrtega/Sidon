import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Logarithmic reserves from a Vinogradov–Korobov width -/

noncomputable section

open Filter Topology

namespace Sidon

theorem tendsto_rpow_div_log_rpow_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => x ^ a / (Real.log x) ^ b) atTop atTop := by
  have hzero := (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < (Real.log x) ^ b / x ^ a := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) _)
      (Real.rpow_pos_of_pos (by linarith) _)
  have hwithin : Tendsto (fun x : ℝ => (Real.log x) ^ b / x ^ a)
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun x : ℝ => ((Real.log x) ^ b / x ^ a)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

def logarithmicZeroFreeWidth (C T : ℝ) : ℝ :=
  C / ((Real.log T) ^ ((2 : ℝ) / 3) *
    (Real.log (Real.log T)) ^ ((1 : ℝ) / 3))

theorem tendsto_logarithmic_width_reserve {C : ℝ} (hC : 0 < C) :
    Tendsto (fun T : ℝ => logarithmicZeroFreeWidth C T * Real.log T /
      Real.log (Real.log T)) atTop atTop := by
  have hbase := (tendsto_rpow_div_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
    (4 / 3)).comp Real.tendsto_log_atTop
  apply (hbase.const_mul_atTop hC).congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hT
  have ha : 0 < Real.log T := by linarith
  have hb : 0 < Real.log (Real.log T) := Real.log_pos hT
  have hpowA : (Real.log T) ^ ((2 : ℝ) / 3) * (Real.log T) ^ ((1 : ℝ) / 3) =
      Real.log T := by
    rw [← Real.rpow_add ha]
    norm_num
  have hpowB : (Real.log (Real.log T)) ^ ((1 : ℝ) / 3) * Real.log (Real.log T) =
      (Real.log (Real.log T)) ^ ((4 : ℝ) / 3) := by
    calc
      _ = (Real.log (Real.log T)) ^ ((1 : ℝ) / 3) *
          (Real.log (Real.log T)) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log (Real.log T)) ^ ((1 : ℝ) / 3 + 1) := (Real.rpow_add hb _ _).symm
      _ = _ := by norm_num
  have hdiv : Real.log T / (Real.log T) ^ ((2 : ℝ) / 3) =
      (Real.log T) ^ ((1 : ℝ) / 3) := by
    apply (div_eq_iff (Real.rpow_pos_of_pos ha _).ne').mpr
    simpa only [mul_comm] using hpowA.symm
  change C * ((Real.log T) ^ ((1 : ℝ) / 3) /
      (Real.log (Real.log T)) ^ ((4 : ℝ) / 3)) = _
  symm
  calc
    _ = C * (Real.log T / (Real.log T) ^ ((2 : ℝ) / 3)) /
        ((Real.log (Real.log T)) ^ ((1 : ℝ) / 3) * Real.log (Real.log T)) := by
      simp only [logarithmicZeroFreeWidth, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hdiv, hpowB]; ring

theorem eventually_logarithmic_width_reserve {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (B : ℝ) : ∀ᶠ T : ℝ in atTop,
      B * Real.log (Real.log T) ≤ δ * logarithmicZeroFreeWidth C T * Real.log T := by
  have hlim := (tendsto_logarithmic_width_reserve hC).const_mul_atTop hδ
  filter_upwards [hlim.eventually_ge_atTop B,
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hbound hT
  have hlog : 0 < Real.log (Real.log T) := Real.log_pos hT
  have h := (le_div_iff₀ hlog).mp (show B ≤
    (δ * logarithmicZeroFreeWidth C T * Real.log T) / Real.log (Real.log T) by
      simpa only [Function.comp_apply, mul_div_assoc, mul_assoc] using hbound)
  exact h

end Sidon
