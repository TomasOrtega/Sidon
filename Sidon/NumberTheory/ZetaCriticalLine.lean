import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Critical-line growth estimates for zeta -/

noncomputable section

namespace Sidon

def zetaCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + t * Complex.I

@[simp] theorem zetaCriticalPoint_re (t : ℝ) : (zetaCriticalPoint t).re = 1 / 2 := by
  simp [zetaCriticalPoint]

@[simp] theorem zetaCriticalPoint_im (t : ℝ) : (zetaCriticalPoint t).im = t := by
  simp [zetaCriticalPoint]

theorem continuous_riemannZeta_criticalPoint :
    Continuous (fun t : ℝ => riemannZeta (zetaCriticalPoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : zetaCriticalPoint t ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hc : Continuous zetaCriticalPoint := by unfold zetaCriticalPoint; fun_prop
  exact (differentiableAt_riemannZeta hs).continuousAt.comp hc.continuousAt

theorem exists_riemannZeta_criticalPoint_bound_on_compact (R : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, |t| ≤ R → ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-R) R)).exists_bound_of_continuousOn
    continuous_riemannZeta_criticalPoint.continuousOn
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC t (abs_le.mp ht)).trans (le_max_left _ _)

theorem rpow_mul_log_le_rpow {x a b : ℝ} (hx : 0 < x) (hab : a < b) :
    x ^ a * Real.log x ≤ (b - a)⁻¹ * x ^ b := by
  have hlog := Real.log_le_rpow_div hx.le (sub_pos.mpr hab)
  calc
    _ ≤ x ^ a * (x ^ (b - a) / (b - a)) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx.le _)
    _ = (b - a)⁻¹ * (x ^ a * x ^ (b - a)) := by ring
    _ = _ := by rw [← Real.rpow_add hx, add_sub_cancel]

theorem sixth_rpow_mul_log_le_three_sixteenths {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 6) * Real.log x ≤ 48 * x ^ ((3 : ℝ) / 16) := by
  have h := rpow_mul_log_le_rpow (a := (1 : ℝ) / 6) (b := (3 : ℝ) / 16)
    hx (by norm_num)
  norm_num only [show ((3 : ℝ) / 16 - 1 / 6)⁻¹ = 48 by norm_num] at h
  exact h

theorem exists_riemannZeta_criticalPoint_growth_of_tail {c C : ℝ}
    (hc : 0 ≤ c)
    (htail : ∀ t : ℝ, 2 ≤ |t| →
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * |t| ^ c) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ D * (1 + |t|) ^ c := by
  obtain ⟨B, hB, hcompact⟩ := exists_riemannZeta_criticalPoint_bound_on_compact 2
  let D := max B C
  have hBD : B ≤ D := le_max_left _ _
  have hCD : C ≤ D := le_max_right _ _
  have hD : 0 < D := by linarith
  refine ⟨D, hD, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · have hpow : 1 ≤ (1 + |t|) ^ c :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hc
    exact (hcompact t ht).trans (hBD.trans (by nlinarith))
  · have hp : |t| ^ c ≤ (1 + |t|) ^ c :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hc
    exact (htail t (le_of_lt (lt_of_not_ge ht))).trans
      (mul_le_mul hCD hp (Real.rpow_nonneg (abs_nonneg t) _) hD.le)

end Sidon
