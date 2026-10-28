module

public import Sidon.NumberTheory.MollifierOptimization

@[expose] public section

/-! # Uniform vertical slices in the geometric Jensen window -/

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem exists_optimizedMollifierSlices :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 →
        ∃ N : ℕ, 131072 ≤ N ∧ T ≤ (N : ℝ) ∧
          ∀ u ∈ Icc σ₀ (4 - σ₀),
            (∫ t in Icc 1 (T + 3),
              ‖mollifierError N ((u : ℂ) + t * Complex.I)‖ ^ 2) ≤
              K * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log T ^ 9 := by
  obtain ⟨K, hK, hbound⟩ := exists_mollifier_optimized_bound
  refine ⟨2048 * K, by positivity, max 131072 (Real.exp 4), ?_⟩
  intro T hT σ₀ hσ₀ hσ₀1
  have hTlarge : (131072 : ℝ) ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT3 : 3 ≤ T := by linarith
  have hlog : 4 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 4) ((le_max_right _ _).trans hT)
    simpa only [Real.log_exp] using hh
  have hR : 1 ≤ T + 3 := by linarith
  have hR0 : 0 < T + 3 := by linarith
  have hRT : T + 3 ≤ 2 * T := by linarith
  have hlogRlo : 2 ≤ Real.log (T + 3) := by
    have hh := Real.log_le_log hT0 (show T ≤ T + 3 by linarith)
    linarith
  have hlogR : Real.log (T + 3) ≤ 2 * Real.log T := by
    have hh := Real.log_le_log hR0 hRT
    rw [Real.log_mul (by norm_num) hT0.ne'] at hh
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    linarith
  have hRN : T + 3 ≤ (⌈T + 3⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨⌈T + 3⌉₊, ?_, by linarith, ?_⟩
  · exact_mod_cast (show (131072 : ℝ) ≤ ⌈T + 3⌉₊ by linarith)
  intro u hu
  have ha : 0 ≤ (11 / 4 : ℝ) * (1 - σ₀) := by positivity
  have ha2 : (11 / 4 : ℝ) * (1 - σ₀) ≤ 2 := by linarith
  have hpower : (T + 3) ^ ((11 / 4 : ℝ) * (1 - σ₀)) ≤
      4 * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := by
    calc
      _ ≤ (2 * T) ^ ((11 / 4 : ℝ) * (1 - σ₀)) := Real.rpow_le_rpow hR0.le hRT ha
      _ = (2 : ℝ) ^ ((11 / 4 : ℝ) * (1 - σ₀)) *
          T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ (2 : ℝ) ^ (2 : ℝ) * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2) (by positivity)
      _ = _ := by norm_num
  have hlogpow : Real.log (T + 3) ^ 9 ≤ 512 * Real.log T ^ 9 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (T + 3)) hlogR 9
    rw [mul_pow] at hh
    norm_num at hh
    exact hh
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR]
  calc
    _ ≤ K * (T + 3) ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log (T + 3) ^ 9 :=
      hbound _ hR hlogRlo σ₀ hσ₀ hσ₀1 u hu.1
    _ ≤ K * (4 * T ^ ((11 / 4 : ℝ) * (1 - σ₀))) * (512 * Real.log T ^ 9) := by gcongr
    _ = _ := by ring

end Sidon
