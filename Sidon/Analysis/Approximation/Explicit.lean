module

public import Sidon.Analysis.Approximation.Uniform

@[expose] public section

/-! # Explicit dimension-dependent trigonometric approximation -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem fejer_error_bound_of_bandwidth {d M : ℕ} {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (hM : 0 < M)
    (hband : 27 * (d : ℝ) * K ^ 2 / ε ^ 3 ≤ M) :
    K * (ε / (3 * K)) + (d : ℝ) / ((M : ℝ) * (ε / (3 * K)) ^ 2) ≤ ε := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hmul : 27 * (d : ℝ) * K ^ 2 ≤ (M : ℝ) * ε ^ 3 :=
    (div_le_iff₀ (pow_pos hε 3)).mp hband
  have htail : (d : ℝ) / ((M : ℝ) * (ε / (3 * K)) ^ 2) ≤ ε / 3 := by
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < (M : ℝ) * (ε / (3 * K)) ^ 2)).mpr
    have heq : ε / 3 * ((M : ℝ) * (ε / (3 * K)) ^ 2) =
        (M : ℝ) * ε ^ 3 / (27 * K ^ 2) := by
      field_simp
      ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 27 * K ^ 2)).mpr
    nlinarith
  have hnear : K * (ε / (3 * K)) = ε / 3 := by field_simp
  rw [hnear]
  linarith

theorem ceil_fejer_bandwidth_le {d : ℕ} (hd : 0 < d) {K ε : ℝ}
    (hK : 1 ≤ K) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (⌈27 * (d : ℝ) * K ^ 2 / ε ^ 3⌉₊ : ℝ) ≤
      28 * (d : ℝ) * K ^ 2 / ε ^ 3 := by
  let A := (d : ℝ) * K ^ 2 / ε ^ 3
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKsq : (1 : ℝ) ≤ K ^ 2 := by nlinarith
  have hεpow : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hε₁
  have hA : 1 ≤ A := by
    apply (le_div_iff₀ (pow_pos hε 3)).mpr
    nlinarith [mul_le_mul hd' hKsq zero_le_one (by positivity : (0 : ℝ) ≤ d)]
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 27 * A)
  have hbound : (⌈27 * A⌉₊ : ℝ) ≤ 28 * A := by linarith
  have heq : 27 * (d : ℝ) * K ^ 2 / ε ^ 3 = 27 * A := by dsimp [A]; ring
  rw [heq]
  convert hbound using 1
  dsimp [A]
  ring

theorem exists_trigonometric_approximation {d : ℕ} (hd : 0 < d)
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (K : NNReal) (hK : 1 ≤ (K : ℝ)) (hLip : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ M ≤ ⌈27 * (d : ℝ) * (K : ℝ) ^ 2 / ε ^ 3⌉₊ ∧
      ∃ a : (Fin d → ℤ) →₀ ℂ,
        (∀ n ∈ a.support, ∀ i, |n i| < (M : ℤ)) ∧ (∀ n, ‖a n‖ ≤ 1) ∧
        ∃ P : C(Fin d → AddCircle (1 : ℝ), ℝ),
          (∀ x, P x ∈ Set.Icc (0 : ℝ) 1) ∧ ‖F - P‖ ≤ ε ∧
          torusPolynomial a = torusComplexify P := by
  let M := ⌈27 * (d : ℝ) * (K : ℝ) ^ 2 / ε ^ 3⌉₊
  have hKp : (0 : ℝ) < K := by linarith
  have hMp : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hband : 27 * (d : ℝ) * (K : ℝ) ^ 2 / ε ^ 3 ≤ M := Nat.le_ceil _
  refine ⟨M, hMp, le_rfl, fejerApproxCoefficients F M, ?_,
    norm_fejerApproxCoefficients_le_one F M hF, fejerApproximation F M, ?_, ?_,
    torusPolynomial_fejerApproxCoefficients F hMp⟩
  · intro n hn i
    exact fejerFrequencyBox_abs_lt (support_fejerApproxCoefficients_subset F M hn) i
  · intro x
    exact ⟨fejerApproximation_nonneg F M (fun x => (hF x).1) x,
      fejerApproximation_le_one F hMp (fun x => (hF x).2) x⟩
  · apply (norm_fejerApproximation_error_le F hF K.coe_nonneg
      (by positivity : (0 : ℝ) < ε / (3 * K)) ?_ hMp).trans
      (fejer_error_bound_of_bandwidth hKp hε hMp hband)
    intro x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul x y

end Sidon
