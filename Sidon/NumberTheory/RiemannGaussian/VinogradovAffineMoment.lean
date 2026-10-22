/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCoarseCongruence
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovPowerSumRigidity

namespace RiemannGaussian.VinogradovAffineMoment
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovCoarseCongruence
theorem weighted_affine_equal_iff {r k : ℕ} (c u v : Fin r → ℤ) {q : ℤ}
    (hq : q ≠ 0) (xi : ℤ) :
    (∀ n, 1 ≤ n → n ≤ k →
      (∑ i, c i * (q * u i + xi) ^ n) = ∑ i, c i * (q * v i + xi) ^ n) ↔
    (∀ n, 1 ≤ n → n ≤ k →
      (∑ i, c i * u i ^ n) = ∑ i, c i * v i ^ n) := by
  constructor
  · intro h n hn hnk
    have ht := translated_power_difference_dvd c
      (fun i => q * v i + xi) (fun i => q * u i + xi) xi 0 (n := n) (by
        intro d hd hdn
        rw [h d hd (hdn.trans hnk), sub_self])
    simp only [add_sub_cancel_right, scaled_power_difference, zero_dvd_iff] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (pow_ne_zero n hq))
  · intro h n hn hnk
    have ht := translated_power_difference_dvd c
      (fun i => q * v i) (fun i => q * u i) (-xi) 0 (n := n) (by
        intro d hd hdn
        rw [scaled_power_difference, h d hd (hdn.trans hnk), sub_self, mul_zero])
    simpa only [sub_neg_eq_add, zero_dvd_iff, sub_eq_zero] using ht

theorem frequency_sum_eq_iff {r k : ℕ} (u v : Fin r → ℤ) :
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (u i)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (v i)) ↔
    ∀ n, 1 ≤ n → n ≤ k → (∑ i, u i ^ n) = ∑ i, v i ^ n := by
  constructor
  · intro h n hn hnk
    have he := congrFun h ⟨n - 1, by omega⟩
    simpa only [Finset.sum_apply, VinogradovPowerSumRigidity.integerFrequency,
      Nat.sub_add_cancel hn] using he
  · intro h
    funext i
    simpa only [Finset.sum_apply, VinogradovPowerSumRigidity.integerFrequency] using
      h (i.val + 1) (by omega) (by omega)

theorem affine_frequency_collision_iff {r k : ℕ} (u v : Fin r → ℤ)
    {q : ℤ} (hq : q ≠ 0) (xi : ℤ) :
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (q * u i + xi)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (q * v i + xi)) ↔
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (u i)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (v i)) := by
  rw [frequency_sum_eq_iff, frequency_sum_eq_iff]
  simpa only [one_mul] using weighted_affine_equal_iff (fun _ => 1) u v hq xi

theorem moment_affine {ι : Type*} [Fintype ι] (r k : ℕ) (v : ι → ℤ)
    {q : ℤ} (hq : q ≠ 0) (xi : ℤ) :
    VinogradovMeanValue.moment r (fun i => VinogradovPowerSumRigidity.integerFrequency k (q * v i + xi)) =
      VinogradovMeanValue.moment r (fun i => VinogradovPowerSumRigidity.integerFrequency k (v i)) := by
  classical
  rw [VinogradovMeanValue.moment_eq_collisionCount, VinogradovMeanValue.moment_eq_collisionCount]
  congr 1
  unfold VinogradovMeanValue.collisionCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    affine_frequency_collision_iff (fun i => v (xy.1 i)) (fun i => v (xy.2 i)) hq xi]

end
end RiemannGaussian.VinogradovAffineMoment
