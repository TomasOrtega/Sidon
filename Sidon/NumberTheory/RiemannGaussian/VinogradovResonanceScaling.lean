/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovExplicitKorobov
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment

namespace RiemannGaussian.VinogradovResonanceScaling
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
open RiemannGaussian.VinogradovExplicitKorobov
def reciprocalScale (r : ℕ) (M : ℝ) (q : ℕ) : ℝ := (1 / ((r : ℝ) * M ^ q)) ^ 2

theorem reciprocalScale_pos {r : ℕ} (hr : 0 < r) {M : ℝ} (hM : 0 < M) (q : ℕ) :
    0 < reciprocalScale r M q := by
  unfold reciprocalScale
  positivity

theorem sqrt_reciprocalScale {r : ℕ} (hr : 0 < r) {M : ℝ} (hM : 0 < M) (q : ℕ) :
    Real.sqrt (reciprocalScale r M q) = 1 / ((r : ℝ) * M ^ q) := by
  rw [reciprocalScale, Real.sqrt_sq_eq_abs, abs_of_pos]
  positivity

theorem reciprocalScale_le_one {r : ℕ} (hr : 0 < r) {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    reciprocalScale r M q ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 1 ≤ (r : ℝ) * M ^ q := one_le_mul_of_one_le_of_one_le hr1 (one_le_pow₀ hM)
  have hi : 1 / ((r : ℝ) * M ^ q) ≤ 1 := (div_le_one (by positivity)).mpr hd
  exact (pow_le_pow_left₀ (by positivity) hi 2).trans_eq (one_pow 2)

theorem reciprocal_prefactor_le {r : ℕ} (hr : 0 < r) {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    2 / ((reciprocalScale r M q) ^ (1 / 2 : ℝ) *
      (1 - Real.exp (-Real.pi / reciprocalScale r M q))) ≤
      (2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * M ^ q := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have ha := reciprocalScale_pos hr hMpos q
  have ha1 := reciprocalScale_le_one hr hM q
  have hden0 : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have he : -Real.pi / reciprocalScale r M q ≤ -Real.pi := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [Real.pi_pos, mul_le_mul_of_nonneg_left ha1 Real.pi_pos.le]
  have hden : 1 - Real.exp (-Real.pi) ≤ 1 - Real.exp (-Real.pi / reciprocalScale r M q) := by
    linarith only [Real.exp_le_exp.mpr he]
  rw [← Real.sqrt_eq_rpow, sqrt_reciprocalScale hr hMpos]
  calc
    _ ≤ 2 / ((1 / ((r : ℝ) * M ^ q)) * (1 - Real.exp (-Real.pi))) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hden (by positivity))
    _ = _ := by field_simp

theorem power_phase_width_identity (k r : ℕ) (hr : 0 < r) {M : ℝ} (hM : 0 < M) (j : Fin k) :
    Real.sqrt (reciprocalScale r M (j.val + 1)) /
      |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| =
      (2 * Real.pi * (j.val + 1) / (r : ℝ)) *
        (M ^ (3 * (j.val + 1)) / M ^ (2 * k)) := by
  rw [sqrt_reciprocalScale hr hM, abs_phaseCoefficients k _ (by positivity),
    abs_of_pos (pow_pos hM _)]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hq0 : ((j.val : ℝ) + 1) ≠ 0 := by positivity
  have he : (M ^ 4) ^ (j.val + 1) = M ^ (j.val + 1) * M ^ (3 * (j.val + 1)) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

end
end RiemannGaussian.VinogradovResonanceScaling
