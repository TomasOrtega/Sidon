module

public import Sidon.NumberTheory.MollifierSymmetry
public import Sidon.NumberTheory.WeylZeta

@[expose] public section

/-! # Weyl growth and the critical-line mollifier mean square -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

theorem exists_mollifierError_critical_cumulative_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 0 ≤ T →
      (∫ t in Set.Icc (-T) T, ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) ≤
        K * (1 + Real.log N) * (T + N) * (1 + T) ^ ((3 : ℝ) / 8) := by
  obtain ⟨C, hC, hW⟩ := exists_riemannZeta_critical_growth
  refine ⟨48 * C ^ 2 + 4, by positivity, ?_⟩
  intro N hN T hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hp : 1 ≤ (1 + T) ^ ((3 : ℝ) / 8) := Real.one_le_rpow (by linarith) (by norm_num)
  let B : ℝ := 2 * C ^ 2 * (1 + T) ^ ((3 : ℝ) / 8)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 ≤
        B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2 := by
    have hz : ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * (1 + T) ^ ((3 : ℝ) / 16) := by
      apply (hW t).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [abs_of_nonneg ht.1]
      linarith [ht.2]
    have hz2 : ‖riemannZeta (zetaCriticalPoint t)‖ ^ 2 ≤
        C ^ 2 * (1 + T) ^ ((3 : ℝ) / 8) := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have hpow : ((1 + T) ^ ((3 : ℝ) / 16)) ^ 2 = (1 + T) ^ ((3 : ℝ) / 8) := by
        calc
          _ = (1 + T) ^ (((3 : ℝ) / 16) * 2) := by
            rw [Real.rpow_mul (by positivity : 0 ≤ 1 + T), Real.rpow_two]
          _ = _ := by norm_num
      rw [mul_pow, hpow] at hh
      exact hh
    have he : ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 ≤
        2 * ‖riemannZeta (zetaCriticalPoint t)‖ ^ 2 *
          ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2 := by
      have hh := norm_sub_le
        (riemannZeta (zetaCriticalPoint t) * dirichletMollifier N (zetaCriticalPoint t)) (1 : ℂ)
      rw [norm_mul, norm_one] at hh
      change ‖mollifierError N (zetaCriticalPoint t)‖ ≤ _ at hh
      have hh' := pow_le_pow_left₀ (norm_nonneg _) hh 2
      nlinarith [sq_nonneg (‖riemannZeta (zetaCriticalPoint t)‖ *
        ‖dirichletMollifier N (zetaCriticalPoint t)‖ - 1)]
    exact he.trans (by
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_right hz2
        (sq_nonneg ‖dirichletMollifier N (zetaCriticalPoint t)‖)])
  have hcM : Continuous (fun t : ℝ => dirichletMollifier N (zetaCriticalPoint t)) :=
    (differentiable_dirichletMollifier N).continuous.comp (by unfold zetaCriticalPoint; fun_prop)
  have hce : Continuous (fun t : ℝ => ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) := by
    have hh : Continuous (fun t : ℝ => mollifierError N (zetaCriticalPoint t)) :=
      (continuous_riemannZeta_criticalPoint.mul hcM).sub continuous_const
    simpa only [Function.comp_def] using (continuous_pow 2).comp hh.norm
  have hci : Continuous (fun t : ℝ => B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2) :=
    (hcM.norm.pow 2).const_mul B |>.add continuous_const
  have hint : (∫ t in (0 : ℝ)..T, ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) ≤
      B * (12 * (T + N) * (1 + Real.log N)) + 2 * T := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..T, (B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2) :=
        intervalIntegral.integral_mono_on hT (hce.intervalIntegrable _ _)
          (hci.intervalIntegrable _ _) hpoint
      _ = B * (∫ t in (0 : ℝ)..T, ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2) + 2 * T := by
        have hiB : IntervalIntegrable (fun t : ℝ =>
            B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2) volume 0 T :=
          ((hcM.norm.pow 2).const_mul B).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hiB intervalIntegrable_const,
          intervalIntegral.integral_const_mul]
        simp [mul_comm]
      _ ≤ _ := by
        gcongr
        exact integral_dirichletMollifier_critical_norm_sq_le hN hT
  have heven (t : ℝ) : ‖mollifierError N (zetaCriticalPoint (-t))‖ ^ 2 =
      ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 := by
    have heq : zetaCriticalPoint (-t) = conj (zetaCriticalPoint t) := by
      apply Complex.ext <;> norm_num [zetaCriticalPoint]
    rw [heq, mollifierError_conj, Complex.norm_conj]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    integral_neg_pos_eq_two_of_even hce heven]
  have htail : T ≤ (1 + Real.log N) * (T + N) * (1 + T) ^ ((3 : ℝ) / 8) := by
    calc
      T ≤ T + N := le_add_of_nonneg_right (Nat.cast_nonneg N)
      _ ≤ (1 + Real.log N) * (T + N) := le_mul_of_one_le_left (by positivity) hlog
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp
  dsimp [B] at hint
  nlinarith

end Sidon
