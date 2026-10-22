import Sidon.Transference.FourierNorm
import Sidon.Transference.PositiveMax

/-! # Polynomial evaluation in the real Fourier dual norm -/

noncomputable section

namespace Sidon

variable {ι : Type*} [Fintype ι]

namespace FourierSpace

variable {N : ℕ}

omit [Fintype ι] in
theorem aeval_apply (φ : ι → FourierSpace N) (P : MvPolynomial ι ℝ) (x : Fin N) :
    (MvPolynomial.aeval φ P) x = MvPolynomial.aeval (fun i => φ i x) P := by
  let e : FourierSpace N →ₐ[ℝ] ℝ := Pi.evalAlgHom ℝ (fun _ : Fin N => ℝ) x
  have h : e.comp (MvPolynomial.aeval φ) = MvPolynomial.aeval (fun i => φ i x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun h P

omit [Fintype ι] in
/-- A bound depending only on the polynomial and the bound on its variables. -/
theorem exists_dualNorm_aeval_bound (P : MvPolynomial ι ℝ) {L : ℝ} (hL : 1 ≤ L) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (N : ℕ) (φ : ι → FourierSpace N),
      (∀ i, dualNorm (φ i) ≤ L) → dualNorm (MvPolynomial.aeval φ P) ≤ B := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨max 1 |a|, le_max_left _ _, fun N φ hφ => ?_⟩
    rw [MvPolynomial.aeval_C]
    have heq : algebraMap ℝ (FourierSpace N) a = a • (1 : FourierSpace N) := by
      funext i
      change a = a * 1
      ring
    rw [heq, dualNorm_smul]
    exact (mul_le_of_le_one_right (abs_nonneg a) dualNorm_one_le).trans (le_max_right _ _)
  | add P Q hP hQ =>
    obtain ⟨BP, hBP, hP⟩ := hP
    obtain ⟨BQ, hBQ, hQ⟩ := hQ
    refine ⟨BP + BQ, by linarith, fun N φ hφ => ?_⟩
    rw [map_add]
    exact (dualNorm_add_le _ _).trans (add_le_add (hP N φ hφ) (hQ N φ hφ))
  | mul_X P i hP =>
    obtain ⟨B, hB, hP⟩ := hP
    refine ⟨B * L, (by nlinarith), fun N φ hφ => ?_⟩
    rw [map_mul, MvPolynomial.aeval_X]
    exact (dualNorm_mul_le _ _).trans (mul_le_mul (hP N φ hφ) (hφ i)
      (dualNorm_nonneg _) (by linarith))

end FourierSpace

end Sidon
