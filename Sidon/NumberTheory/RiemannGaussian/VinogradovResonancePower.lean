/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

namespace RiemannGaussian.VinogradovResonancePower
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
open RiemannGaussian.VinogradovResonanceScaling
theorem doubled_degree_sum (k : ℕ) : (∑ j : Fin k, 2 * (j.val + 1)) = k * (k + 1) := by
  change (∑ j : Fin k, (fun n : ℕ => 2 * (n + 1)) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => 2 * (n + 1)) k]
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem full_coordinate_power_le (r s : ℕ) (hr : 0 < r) {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    (2 / ((reciprocalScale r M q) ^ (1 / 2 : ℝ) *
      (1 - Real.exp (-Real.pi / reciprocalScale r M q)))) *
      (2 * (s : ℝ) * M ^ q + 1) ≤
      ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * (2 * (s : ℝ) + 1)) * M ^ (2 * q) := by
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hcard : 2 * (s : ℝ) * M ^ q + 1 ≤ (2 * (s : ℝ) + 1) * M ^ q := by
    nlinarith only [one_le_pow₀ (n := q) hM]
  calc
    _ ≤ ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * M ^ q) *
        ((2 * (s : ℝ) + 1) * M ^ q) :=
      mul_le_mul (reciprocal_prefactor_le hr hM q) hcard (by positivity) (by positivity)
    _ = _ := by rw [show 2 * q = q + q by omega, pow_add]; ring

end
end RiemannGaussian.VinogradovResonancePower
