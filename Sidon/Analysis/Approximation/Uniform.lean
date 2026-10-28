module

public import Sidon.Analysis.Approximation.Convolution

@[expose] public section

/-! # Uniform Lipschitz error bounds for tensor Fejér approximation -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

variable {d : ℕ}

private theorem torus_integrable {f : (Fin d → AddCircle (1 : ℝ)) → ℝ}
    (hf : Continuous f) : Integrable f (torusHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fejerApproximation_error_le (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η)
    (hLip : ∀ x y, |F x - F y| ≤ K * ‖x - y‖)
    {M : ℕ} (hM : 0 < M) (x : Fin d → AddCircle (1 : ℝ)) :
    |F x - fejerApproximation F M x| ≤ K * η + (d : ℝ) / ((M : ℝ) * η ^ 2) := by
  let Λ := tensorFejer d M
  let b := 1 / ((M : ℝ) * η ^ 2)
  have hnonneg : ∀ y, 0 ≤ ∑ i : Fin d, b * tensorFejerOmit M i y := by
    intro y
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by dsimp [b]; positivity) (tensorFejerOmit_nonneg M i y)
  have hpoint : ∀ y, |(F x - F (x - y)) * Λ y| ≤
      K * η * Λ y + ∑ i : Fin d, b * tensorFejerOmit M i y := by
    intro y
    rw [abs_mul, abs_of_nonneg (tensorFejer_nonneg d M y)]
    by_cases hy : ‖y‖ ≤ η
    · have hsmall : |F x - F (x - y)| ≤ K * η := by
        have h := hLip x (x - y)
        rw [sub_sub_cancel] at h
        exact h.trans (mul_le_mul_of_nonneg_left hy hK)
      exact (mul_le_mul_of_nonneg_right hsmall (tensorFejer_nonneg d M y)).trans
        (le_add_of_nonneg_right (hnonneg y))
    · have hlarge : |F x - F (x - y)| ≤ 1 := by
        exact abs_le.mpr ⟨by linarith [(hF x).1, (hF (x - y)).2],
          by linarith [(hF x).2, (hF (x - y)).1]⟩
      calc
        |F x - F (x - y)| * Λ y ≤ Λ y :=
          mul_le_of_le_one_left (tensorFejer_nonneg d M y) hlarge
        _ ≤ ∑ i : Fin d, b * tensorFejerOmit M i y :=
          tensorFejer_le_sum_omit_of_norm_gt hη y (lt_of_not_ge hy)
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (mul_nonneg hK hη.le)
          (tensorFejer_nonneg d M y))
  have hdiff : F x - fejerApproximation F M x =
      ∫ y, (F x - F (x - y)) * Λ y ∂torusHaar d := by
    simp_rw [sub_mul]
    rw [integral_sub (torus_integrable (by fun_prop)) (torus_integrable (by fun_prop)),
      integral_const_mul, integral_tensorFejer d hM, mul_one]
    rfl
  rw [hdiff]
  calc
    _ ≤ ∫ y, |(F x - F (x - y)) * Λ y| ∂torusHaar d := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y => (F x - F (x - y)) * Λ y)
    _ ≤ ∫ y, K * η * Λ y + ∑ i : Fin d, b * tensorFejerOmit M i y ∂torusHaar d :=
      integral_mono (torus_integrable (by fun_prop)) (torus_integrable (by fun_prop)) hpoint
    _ = _ := by
      rw [integral_add (torus_integrable (by fun_prop)) (torus_integrable (by fun_prop)),
        integral_const_mul, integral_tensorFejer d hM,
        integral_finset_sum _ (fun _ _ => torus_integrable (by fun_prop))]
      simp only [integral_const_mul, integral_tensorFejerOmit hM, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [b]
      ring

theorem norm_fejerApproximation_error_le (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η)
    (hLip : ∀ x y, |F x - F y| ≤ K * ‖x - y‖) {M : ℕ} (hM : 0 < M) :
    ‖F - fejerApproximation F M‖ ≤ K * η + (d : ℝ) / ((M : ℝ) * η ^ 2) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
    fejerApproximation_error_le F hF hK hη hLip hM x

end Sidon
