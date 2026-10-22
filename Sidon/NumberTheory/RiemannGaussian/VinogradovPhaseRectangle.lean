/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovExplicitKorobov
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceWindow

namespace RiemannGaussian.VinogradovPhaseRectangle
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovExplicitKorobov RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
open RiemannGaussian.VinogradovResonanceScaling RiemannGaussian.VinogradovResonanceWindow
theorem coefficient_band_nonzero (k : ℕ) {T Z t z : ℝ}
    (hT : 0 < T) (hZ : 0 < Z) (htlo : T ≤ t) (hzlo : Z ≤ z) (j : Fin k) :
    VinogradovKorobovMoment.phaseCoefficients k t z j ≠ 0 := by
  have ht : 0 < t := hT.trans_le htlo
  have hz : 0 < z := hZ.trans_le hzlo
  apply abs_pos.mp
  rw [abs_phaseCoefficients k t hz j, abs_of_pos ht]
  positivity

theorem coefficient_rectangle_bounds (k : ℕ) {T₀ T₁ Z₀ Z₁ t z : ℝ}
    (hT₀ : 0 < T₀) (hZ₀ : 0 < Z₀) (htlo : T₀ ≤ t) (hthi : t ≤ T₁)
    (hzlo : Z₀ ≤ z) (hzhi : z ≤ Z₁) (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k T₀ Z₁ j| ≤
      |VinogradovKorobovMoment.phaseCoefficients k t z j| ∧
    |VinogradovKorobovMoment.phaseCoefficients k t z j| ≤
      |VinogradovKorobovMoment.phaseCoefficients k T₁ Z₀ j| := by
  have ht := hT₀.trans_le htlo
  have hT₁ := ht.trans_le hthi
  have hz := hZ₀.trans_le hzlo
  have hZ₁ := hz.trans_le hzhi
  rw [abs_phaseCoefficients k T₀ hZ₁ j, abs_of_pos hT₀,
    abs_phaseCoefficients k t hz j, abs_of_pos ht,
    abs_phaseCoefficients k T₁ hZ₀ j, abs_of_pos hT₁]
  constructor <;> gcongr

theorem lower_power_coefficient_identity (k : ℕ) {M B : ℝ} (hM : 0 < M) (hB : 0 < B)
    (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k - 2)) (B * M ^ 4) j| =
      |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| /
        (B ^ (j.val + 1) * M ^ 2) := by
  rw [abs_phaseCoefficients k _ (by positivity), abs_of_pos (pow_pos hM _),
    abs_phaseCoefficients k _ (by positivity), abs_of_pos (pow_pos hM _), mul_pow]
  have hk : 2 ≤ 2 * k := by have hj := j.isLt; omega
  have he : M ^ (2 * k - 2) * M ^ 2 = M ^ (2 * k) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [← he]
  field_simp

theorem power_rectangle_coefficient_bounds (k : ℕ) {M B t z : ℝ}
    (hM : 0 < M) (hB : 0 < B)
    (htlo : M ^ (2 * k - 2) ≤ t) (hthi : t ≤ M ^ (2 * k))
    (hzlo : M ^ 4 ≤ z) (hzhi : z ≤ B * M ^ 4) (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| /
        (B ^ (j.val + 1) * M ^ 2) ≤ |VinogradovKorobovMoment.phaseCoefficients k t z j| ∧
    |VinogradovKorobovMoment.phaseCoefficients k t z j| ≤
      |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| := by
  have h := coefficient_rectangle_bounds k (pow_pos hM _) (pow_pos hM _)
    htlo hthi hzlo hzhi j
  rw [lower_power_coefficient_identity k hM hB j] at h
  exact h

theorem power_rectangle_unwrapped (k s : ℕ) {M B t z : ℝ}
    (hM : 1 ≤ M) (hB : 0 < B) (hsM : (s : ℝ) ≤ M)
    (htlo : M ^ (2 * k - 2) ≤ t) (hthi : t ≤ M ^ (2 * k))
    (hzlo : M ^ 4 ≤ z) (hzhi : z ≤ B * M ^ 4)
    (j : Fin k) (hwindow : 2 * k < 3 * (j.val + 1)) :
    |VinogradovKorobovMoment.phaseCoefficients k t z j| * ((s : ℝ) * M ^ (j.val + 1)) ≤ 1 / 2 := by
  have hMpos := zero_lt_one.trans_le hM
  have hc := (power_rectangle_coefficient_bounds k hMpos hB htlo hthi hzlo hzhi j).2
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    (power_phase_unwrapped k s hM hsM j hwindow)

theorem power_rectangle_width_le (k : ℕ) {M B t z a : ℝ}
    (hM : 0 < M) (hB : 0 < B)
    (htlo : M ^ (2 * k - 2) ≤ t) (hthi : t ≤ M ^ (2 * k))
    (hzlo : M ^ 4 ≤ z) (hzhi : z ≤ B * M ^ 4) (j : Fin k) :
    Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k t z j| ≤
      (B ^ (j.val + 1) * M ^ 2) *
        (Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j|) := by
  have hc := (power_rectangle_coefficient_bounds k hM hB htlo hthi hzlo hzhi j).1
  have hbase : 0 < |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| :=
    abs_pos.mpr (power_phase_nonzero k hM j)
  calc
    _ ≤ Real.sqrt a /
        (|VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| /
          (B ^ (j.val + 1) * M ^ 2)) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg a) (by positivity) hc
    _ = _ := by field_simp

end
end RiemannGaussian.VinogradovPhaseRectangle
