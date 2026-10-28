module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

@[expose] public section

namespace RiemannGaussian.VinogradovGaussianCost
noncomputable section
open scoped BigOperators

theorem half_le_tail_denominator : (1 / 2 : ℝ) ≤ 1 - Real.exp (-Real.pi) := by
  have hp : (2 : ℝ) ≤ Real.exp Real.pi := by
    have h := Real.add_one_le_exp Real.pi
    linarith only [h, Real.pi_gt_three]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  rw [Real.exp_neg, inv_eq_one_div]
  linarith only [h]

theorem scalar_prefactor_le {k r : ℕ} (hk : k ≤ r) (hr : 1 ≤ r) :
    (2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)) ≤ 48 * (r : ℝ) ^ 2 := by
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
  have hden := half_le_tail_denominator
  have hden0 : 0 < 1 - Real.exp (-Real.pi) := by linarith only [hden]
  have hG : 2 * (r : ℝ) / (1 - Real.exp (-Real.pi)) ≤ 4 * (r : ℝ) := by
    apply (div_le_iff₀ hden0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ r by positivity)]
  have hterm : 2 * Real.pi * (k : ℝ) / (r : ℝ) ≤ 8 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hrr)).mpr
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (show (0 : ℝ) ≤ k by positivity)
    nlinarith only [hp, hkr]
  have hF : 2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ) ≤ 12 * (r : ℝ) := by
    linarith only [hterm, hrr]
  calc
    _ ≤ (4 * (r : ℝ)) * (12 * (r : ℝ)) := mul_le_mul hG hF (by positivity) (by positivity)
    _ = _ := by ring

theorem coordinate_constant_le (k : ℕ) (hk : 12 ≤ k) :
    let r := (k + 1) * k
    (4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ))) ≤ (2 : ℝ) ^ (7 * k) := by
  let r := (k + 1) * k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hr : 1 ≤ r := by dsimp only [r]; nlinarith only [hk]
  have hkr : k ≤ r := by dsimp only [r]; nlinarith only [hk]
  have hb := scalar_prefactor_le hkr hr
  have hrk : (r : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
    dsimp only [r]
    push_cast
    nlinarith only [hk1, sq_nonneg ((k : ℝ) - 1)]
  have hs : (r : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hrk 2
    nlinarith only [h]
  have hkpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hsmall : (192 : ℝ) ≤ (2 : ℝ) ^ k := by
    apply le_trans (show (192 : ℝ) ≤ (2 : ℝ) ^ 8 by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hkp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) k) hkpow 4
  calc
    _ ≤ (4 : ℝ) ^ k * (192 * (k : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_left (hb.trans _) (by positivity)
      nlinarith only [hs]
    _ ≤ (4 : ℝ) ^ k * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ 4) := by gcongr
    _ = _ := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

theorem complete_gaussian_constant_le (k : ℕ) (hk : 12 ≤ k) :
    let r := (k + 1) * k
    Real.exp ((k : ℝ) * Real.pi / 4) *
      ((4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
        (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)))) ^ k ≤
      (2 : ℝ) ^ (9 * k ^ 2) := by
  let r := (k + 1) * k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he : Real.exp ((k : ℝ) * Real.pi / 4) ≤ (2 : ℝ) ^ (2 * k) := by
    calc
      _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by
        have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hk0
        linarith only [hp])
      _ = Real.exp 1 ^ k := by simpa only [mul_one] using Real.exp_nat_mul 1 k
      _ ≤ (4 : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le
        (Real.exp_one_lt_three.le.trans (by norm_num)) _
      _ = _ := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hc := coordinate_constant_le k hk
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    have h := half_le_tail_denominator
    linarith only [h]
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * ((2 : ℝ) ^ (7 * k)) ^ k :=
      mul_le_mul he (pow_le_pow_left₀ (by positivity) hc k) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (2 * k + 7 * k * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith only [hk]

open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel RiemannGaussian.VinogradovIntervalResonance
open RiemannGaussian.VinogradovResonanceScaling RiemannGaussian.VinogradovResonanceWindow RiemannGaussian.VinogradovResonancePower
open RiemannGaussian.VinogradovRectangleResonance RiemannGaussian.VinogradovPhaseRectangle
theorem actual_gaussian_resonance_le (k : ℕ) (hk : 12 ≤ k) :
    let r := (k + 1) * k
    ∀ M : ℕ, 1 ≤ M → r ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, b ≤ M) →
      Real.exp ((k : ℝ) * Real.pi / 4) *
        resonanceEnvelope r (fun j => reciprocalScale r M (j.val + 1))
          (VinogradovKorobovMoment.phaseCoefficients k t z)
          (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
        (2 : ℝ) ^ (9 * k ^ 2) * (M : ℝ) ^ (k * (k + 1) - rectangleSaving k) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  dsimp only
  intro M hM hrM t z htlo hthi hzlo hzhi B hB
  have h := actual_resonance_le_explicit k r r hr M hM hrM t z htlo hthi hzlo hzhi B hB
  have hscaled := mul_le_mul_of_nonneg_left h (Real.exp_pos ((k : ℝ) * Real.pi / 4)).le
  apply hscaled.trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (complete_gaussian_constant_le k hk) (by positivity)

end
end RiemannGaussian.VinogradovGaussianCost
