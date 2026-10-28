module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance

@[expose] public section

namespace RiemannGaussian.VinogradovRectanglePowerSaving
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovRectangleResonance
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovResonanceScaling
theorem rectangleSaving_le_dimension (k : ℕ) : rectangleSaving k ≤ k * (k + 1) := by
  rw [rectangleSaving_eq]
  exact Nat.mul_le_mul (by omega) (by omega)

theorem one_lt_rectangleSaving (k : ℕ) (hk : 12 ≤ k) : 1 < rectangleSaving k := by
  rw [rectangleSaving_eq]
  have hm : 3 ≤ k - 2 * k / 3 - 1 := by omega
  have h := Nat.mul_le_mul hm (show 2 ≤ k - 2 * k / 3 - 2 by omega)
  omega

theorem rectangle_logarithmic_error_le (k : ℕ) {M : ℕ} (hM : 0 < M) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {t z : ℝ} (ht : 0 ≤ t)
    (hti : t ≤ (M : ℝ) ^ (2 * k)) (hz : (M : ℝ) ^ 4 ≤ z) :
    ‖(∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase
        t z ((b.val + 1 : ℕ) : ℝ) c) -
      ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k
        t z ((b.val + 1 : ℕ) : ℝ) c‖ ≤ 1 / ((k : ℝ) + 1) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hZ : 0 < z := (pow_pos hMpos 4).trans_le hz
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  have h := VinogradovKorobovBilinearPhase.sum_error_le_card (Finset.univ : Finset (Fin M)) B
    (fun b => ((b.val + 1 : ℕ) : ℝ)) (fun c : ℕ => (c : ℝ)) k t
    (z := z) (M₁ := M) (M₂ := M) ((pow_pos hMpos 4).trans_le hz)
    (by intro b _; constructor; positivity; exact_mod_cast b.isLt)
    (fun b hb => ⟨Nat.cast_nonneg b, by exact_mod_cast (hB b hb).2⟩)
  simp only [Finset.card_univ, Fintype.card_fin, abs_of_nonneg ht] at h
  apply h.trans
  calc
    _ ≤ (M : ℝ) * M * ((M : ℝ) ^ (2 * k) *
        ((M : ℝ) * M / (M : ℝ) ^ 4) ^ (k + 1) / (k + 1)) := by gcongr
    _ = _ := by
      have he : (M : ℝ) * M / (M : ℝ) ^ 4 = 1 / (M : ℝ) ^ 2 := by field_simp
      rw [he, div_pow, one_pow, ← pow_mul]
      field_simp
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      ring

end
end RiemannGaussian.VinogradovRectanglePowerSaving
