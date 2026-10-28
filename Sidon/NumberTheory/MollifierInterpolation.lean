module

public import Sidon.NumberTheory.MollifierGaussian
public import Sidon.NumberTheory.MollifierLeftEndpoint
public import Sidon.NumberTheory.GaussianCumulative

@[expose] public section

/-! # Unconditional interpolation of the actual balanced mollifier's mean squares -/

noncomputable section

open MeasureTheory Set Complex.HadamardThreeLines
open scoped Topology

namespace Sidon

theorem gaussianMollifier_sq_le_weighted_error {N : ℕ} {R σ t : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) (hσ1 : σ ≠ 1) :
    ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp 6 * (Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro hh
    exact hσ1 (by have he := congrArg Complex.re hh; simpa [hsre] using he)
  have hR0 : 0 < R := by linarith
  have hu : σ ^ 2 / R ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    nlinarith
  have hpole := norm_poleRemovedMollifierError_le (N := N) (s := s)
    (by rw [hsre]; linarith) hs1
  have he : (Real.exp ((σ ^ 2 - t ^ 2) / R ^ 2)) ^ 2 ≤
      Real.exp 6 * Real.exp (-2 * t ^ 2 / R ^ 2) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    have heq : 2 * ((σ ^ 2 - t ^ 2) / R ^ 2) =
        2 * (σ ^ 2 / R ^ 2) + -(2 * t ^ 2) / R ^ 2 := by ring
    linarith
  change ‖gaussianMollifier N R s‖ ^ 2 ≤ _
  rw [norm_gaussianMollifier N hR0.ne', hsre, hsim, mul_pow]
  have hh := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpole 2) he
    (by positivity) (sq_nonneg ‖mollifierError N s‖)
  convert hh using 1 <;> dsimp [s] <;> ring

theorem verticalL2_gaussianMollifier_le_of_cumulative {N : ℕ} {R σ K p : ℝ}
    (hR : 1 ≤ R) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) (hσ1 : σ ≠ 1)
    (hK : 0 ≤ K) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * (U + N) * (1 + U) ^ p) :
    verticalL2 (gaussianMollifier N R) σ ≤
      Real.exp 6 * gaussianCumulativeConstant * K * (R + N) * R ^ p := by
  have hc : Continuous (fun t : ℝ => ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) :=
    (continuous_pow 2).comp (continuous_mollifierError_vertical N hσ1).norm
  obtain ⟨hi, hbound⟩ := gaussian_integral_of_cumulative hc (fun _ => sq_nonneg _)
    hK hR (Nat.cast_nonneg N) hp hp1 hcum
  unfold verticalL2
  calc
    _ ≤ ∫ t : ℝ, Real.exp 6 * (Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
      apply integral_mono (integrable_gaussianMollifier_norm_sq N hR hσ hσ') (hi.const_mul _)
      intro t
      exact gaussianMollifier_sq_le_weighted_error hR hσ hσ' hσ1
    _ = Real.exp 6 * ∫ t : ℝ, Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg 6)
      convert hh using 1 <;> ring

theorem exists_verticalL2_gaussianMollifier_left_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ R : ℝ, 1 ≤ R →
      verticalL2 (gaussianMollifier N R) (1 / 2) ≤
        K * (1 + Real.log N) * (R + N) * R ^ ((3 : ℝ) / 8) := by
  obtain ⟨K, hK, hc⟩ := exists_mollifierError_critical_cumulative_bound
  refine ⟨Real.exp 6 * gaussianCumulativeConstant * K, by
    exact mul_pos (mul_pos (Real.exp_pos _) gaussianCumulativeConstant_pos) hK, ?_⟩
  intro N hN R hR
  have hlog : 0 ≤ 1 + Real.log N := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.log_nonneg hn]
  have hh := verticalL2_gaussianMollifier_le_of_cumulative (N := N) (σ := 1 / 2)
    hR (by norm_num) (by norm_num) (by norm_num) (mul_nonneg hK.le hlog)
    (p := 3 / 8) (by norm_num) (by norm_num) (fun U hU => by
      simpa [zetaCriticalPoint, mul_assoc] using hc N hN U hU)
  convert hh using 1 <;> ring

theorem verticalL2_gaussianMollifier_right_bound {N : ℕ} (hN : 1 ≤ N)
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    verticalL2 (gaussianMollifier N R) (1 + δ) ≤
      (4096 * Real.exp 6 * gaussianCumulativeConstant) * (R + N) / ((N : ℝ) * δ ^ 8) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc (U : ℝ) (hU : 0 ≤ U) :
      (∫ t in Icc (-U) U, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
        (4096 / ((N : ℝ) * δ ^ 8)) * (U + N) * (1 + U) ^ (0 : ℝ) := by
    have hh := integral_mollifierError_right_symmetric_le hN hδ (by linarith) hU
    apply hh.trans_eq
    simp only [Real.rpow_zero, mul_one]
    field_simp <;> ring
  have hh := verticalL2_gaussianMollifier_le_of_cumulative hR (σ := 1 + δ)
    (by linarith) (by linarith) (by linarith) (by positivity)
    (p := 0) (by norm_num) (by norm_num) hc
  simp only [Real.rpow_zero, mul_one] at hh
  convert hh using 1 <;> ring

theorem integral_mollifierError_le_gaussianL2 {N : ℕ} {R σ : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    (∫ t in (1 : ℝ)..R, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      8 * Real.exp 2 * verticalL2 (gaussianMollifier N R) σ := by
  have hce : ContinuousOn
      (fun t : ℝ => ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) (Icc 1 R) := by
    intro t ht
    have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := by
      intro heq
      have hh := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add,
        Complex.one_im] at hh
      linarith [ht.1]
    have harg : ContinuousAt (fun v : ℝ => (σ : ℂ) + v * Complex.I) t := by fun_prop
    have hcomp : ContinuousAt (fun v : ℝ => mollifierError N ((σ : ℂ) + v * Complex.I)) t :=
      ContinuousAt.comp' (f := fun v : ℝ => (σ : ℂ) + v * Complex.I) (x := t)
        (analyticAt_mollifierError N hs1).continuousAt harg
    exact (hcomp.norm.pow 2).continuousWithinAt
  have hcg : Continuous (fun t : ℝ => gaussianMollifier N R ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (analyticAt_gaussianMollifier N R ?_).continuousAt.comp (by fun_prop)
    apply RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero
    simpa using (show 0 ≤ σ by linarith)
  have hig := integrable_gaussianMollifier_norm_sq N hR hσ hσ'
  calc
    _ ≤ ∫ t in (1 : ℝ)..R, 8 * Real.exp 2 *
        ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hR (hce.intervalIntegrable_of_Icc hR)
        (((hcg.norm.pow 2).const_mul _).intervalIntegrable _ _)
      intro t ht
      exact mollifierError_sq_le_gaussianMollifier_sq hR (by simpa using hσ)
        (by simpa using hσ') (by simpa [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])] using ht.1)
        (by simpa [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])] using ht.2)
    _ = 8 * Real.exp 2 * ∫ t in (1 : ℝ)..R,
        ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [intervalIntegral.integral_of_le hR]
      exact setIntegral_le_integral hig (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

theorem integral_mollifierError_interpolation {N : ℕ} {R δ σ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hσ : σ ∈ Icc (1 / 2) (1 + δ)) :
    (∫ t in (1 : ℝ)..R, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      8 * Real.exp 2 *
        (verticalL2 (gaussianMollifier N R) (1 / 2) ^
          (1 - (σ - 1 / 2) / (1 + δ - 1 / 2)) *
        verticalL2 (gaussianMollifier N R) (1 + δ) ^
          ((σ - 1 / 2) / (1 + δ - 1 / 2))) := by
  apply (integral_mollifierError_le_gaussianL2 hR hσ.1 (by linarith [hσ.2])).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply verticalL2_logConvex (by linarith) hσ
    (analyticOnNhd_gaussianMollifier N R (by norm_num))
    (bddAbove_gaussianMollifier N hR (by norm_num) (by linarith))
  intro u hu
  exact integrable_gaussianMollifier_norm_sq N hR hu.1 (by linarith [hu.2])

end Sidon
