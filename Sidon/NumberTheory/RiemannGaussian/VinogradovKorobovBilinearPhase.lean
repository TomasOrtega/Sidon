module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovLogPhase

@[expose] public section

namespace RiemannGaussian.VinogradovKorobovBilinearPhase
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovKorobovLogPhase
def polynomial (k : ℕ) (t z a b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    (-t * (-1 : ℝ) ^ j / ((j + 1) * z ^ (j + 1))) * a ^ (j + 1) * b ^ (j + 1)

theorem polynomial_eq (k : ℕ) (t z a b : ℝ) :
    polynomial k t z a b = -t * logarithmPolynomial k (a * b / z) := by
  unfold polynomial logarithmPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_pow, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def logarithmicPhase (t z a b : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log (1 + a * b / z) : ℝ) : ℂ) * Complex.I)

def polynomialPhase (k : ℕ) (t z a b : ℝ) : ℂ :=
  Complex.exp (((polynomial k t z a b : ℝ) : ℂ) * Complex.I)

theorem shifted_cpow_eq (t : ℝ) {z a b : ℝ} (hz : 0 < z) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((z + a * b : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      Complex.exp (((-t * Real.log z : ℝ) : ℂ) * Complex.I) * logarithmicPhase t z a b := by
  have hzab : 0 < z + a * b := by positivity
  have hlog : Real.log (z + a * b) = Real.log z + Real.log (1 + a * b / z) := by
    rw [← Real.log_mul hz.ne' (by positivity : (1 + a * b / z : ℝ) ≠ 0)]
    congr 1
    field_simp
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hzab.ne'),
    ← Complex.ofReal_log hzab.le, hlog, logarithmicPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_error_le (k : ℕ) (t : ℝ) {z a b : ℝ}
    (hz : 0 < z) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖logarithmicPhase t z a b - polynomialPhase k t z a b‖ ≤
      |t| * (a * b / z) ^ (k + 1) / (k + 1) := by
  rw [logarithmicPhase, polynomialPhase, polynomial_eq]
  exact VinogradovKorobovLogPhase.phase_error_le k t (by positivity)

theorem weighted_sum_error_le {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (w : ι → κ → ℂ) (k : ℕ) (t : ℝ) {z : ℝ}
    (hz : 0 < z) (ha : ∀ i ∈ A, 0 ≤ a i) (hb : ∀ j ∈ B, 0 ≤ b j) :
    ‖(∑ i ∈ A, ∑ j ∈ B, w i j * logarithmicPhase t z (a i) (b j)) -
      ∑ i ∈ A, ∑ j ∈ B, w i j * polynomialPhase k t z (a i) (b j)‖ ≤
      ∑ i ∈ A, ∑ j ∈ B, ‖w i j‖ * (|t| * (a i * b j / z) ^ (k + 1) / (k + 1)) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (phase_error_le k t hz (ha i hi) (hb j hj)) (norm_nonneg _)

theorem sum_error_le_card {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) {z M₁ M₂ : ℝ}
    (hz : 0 < z)
    (ha : ∀ i ∈ A, 0 ≤ a i ∧ a i ≤ M₁) (hb : ∀ j ∈ B, 0 ≤ b j ∧ b j ≤ M₂) :
    ‖(∑ i ∈ A, ∑ j ∈ B, logarithmicPhase t z (a i) (b j)) -
      ∑ i ∈ A, ∑ j ∈ B, polynomialPhase k t z (a i) (b j)‖ ≤
      (A.card : ℝ) * B.card * (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  have h := weighted_sum_error_le A B a b (fun _ _ => 1) k t hz
    (fun i hi => (ha i hi).1) (fun j hj => (hb j hj).1)
  simp only [one_mul, norm_one] at h
  apply h.trans
  calc
    _ ≤ ∑ _i ∈ A, ∑ _j ∈ B, |t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hab : 0 ≤ a i * b j / z := div_nonneg
        (mul_nonneg (ha i hi).1 (hb j hj).1) hz.le
      have hr : a i * b j / z ≤ M₁ * M₂ / z :=
        div_le_div_of_nonneg_right
          (mul_le_mul (ha i hi).2 (hb j hj).2 (hb j hj).1 ((ha i hi).1.trans (ha i hi).2)) hz.le
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hab hr (k + 1)) (abs_nonneg t)) (by positivity)
    _ = _ := by simp; ring

end
end RiemannGaussian.VinogradovKorobovBilinearPhase
