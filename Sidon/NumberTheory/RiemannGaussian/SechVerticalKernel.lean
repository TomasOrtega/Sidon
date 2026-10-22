/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace RiemannGaussian.SechVerticalKernel
noncomputable section
open MeasureTheory Set Real
def density (u : ℝ) : ℝ := 1 / (2 * Real.cosh u ^ 2)

theorem density_nonneg (u : ℝ) : 0 ≤ density u := by unfold density; positivity

theorem continuous_density : Continuous density := by
  unfold density
  exact continuous_const.div₀ (continuous_const.mul (Real.continuous_cosh.pow 2))
    (fun u => by positivity)

theorem density_le_exp (u : ℝ) : density u ≤ Real.exp (-|u|) := by
  have hc := Real.one_le_cosh u
  have habs : Real.cosh |u| = Real.cosh u := by
    by_cases h : 0 ≤ u
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), Real.cosh_neg]
  have he : Real.exp |u| ≤ 2 * Real.cosh u := by
    rw [← habs, Real.cosh_eq]
    linarith [Real.exp_pos (-|u|)]
  have hd : Real.exp |u| ≤ 2 * Real.cosh u ^ 2 := by nlinarith
  have h := one_div_le_one_div_of_le (Real.exp_pos |u|) hd
  simpa only [density, one_div, Real.exp_neg] using h

theorem integrable_abs_extension {f : ℝ → ℝ} (h : IntegrableOn f (Ioi 0)) :
    Integrable (fun u : ℝ => f |u|) := by
  have hi : IntegrableOn (fun u : ℝ => f |u|) (Ioi 0) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu]
  have hl : IntegrableOn (fun u : ℝ => f |u|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  have hu := hl.union hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hu

theorem integrable_exp_abs : Integrable (fun u : ℝ => Real.exp (-|u|)) :=
  integrable_abs_extension (integrableOn_exp_neg_Ioi 0)

theorem integrable_abs_mul_exp : Integrable (fun u : ℝ => |u| * Real.exp (-|u|)) := by
  apply integrable_abs_extension (f := fun u : ℝ => u * Real.exp (-u))
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
    using h

end
end RiemannGaussian.SechVerticalKernel
