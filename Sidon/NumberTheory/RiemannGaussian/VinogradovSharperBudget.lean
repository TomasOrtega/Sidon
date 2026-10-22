/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
import Sidon.NumberTheory.RiemannGaussian.VinogradovLongBlocks
import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.VinogradovShortDyadic
import Sidon.NumberTheory.RiemannGaussian.VinogradovShortResonance
import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound

namespace RiemannGaussian.VinogradovSharperBudget
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.VinogradovScaleSelection
def delta (n : ℕ) : ℝ := 1 / (4096 * (2 * (n : ℝ) + 1) ^ 2)

def line (n : ℕ) : ℝ := 1 - delta n

def growth (n : ℕ) : ℝ := 2 * delta n / (n : ℝ)

theorem delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity

theorem delta_le (n : ℕ) : delta n ≤ 1 / 4096 := by
  have h : (0 : ℝ) ≤ n := by positivity
  unfold delta
  apply (div_le_iff₀ (by positivity : 0 < 4096 * (2 * (n : ℝ) + 1) ^ 2)).mpr
  nlinarith [sq_nonneg (2 * (n : ℝ))]

theorem line_bounds (n : ℕ) : 1 / 2 ≤ line n ∧ line n < 1 := by
  have h := delta_le n
  have h' := delta_pos n
  unfold line
  constructor <;> linarith

theorem growth_pos {n : ℕ} (hn : 1 ≤ n) : 0 < growth n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold growth
  exact div_pos (mul_pos (by norm_num) (delta_pos n)) hn'

theorem saving_ge {n k : ℕ} (hn : 48 ≤ n) (hk : 12 ≤ k) (hkn : k ≤ 2 * n + 1) :
    2 * delta n ≤ VinogradovShortResonance.saving k / 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnr : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 2 * delta n = 1 / (2048 * (2 * (n : ℝ) + 1) ^ 2) := by
    unfold delta
    field_simp
    ring
  rw [he]
  unfold VinogradovShortResonance.saving
  split_ifs with hk48
  · have hkr : (k : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hkn
    have hsq : (k : ℝ) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < 2048 * (k : ℝ) ^ 2)
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2048))
    calc
      _ ≤ 1 / (2048 * (k : ℝ) ^ 2) := h
      _ = 1 / (512 * (k : ℝ) ^ 2) / 4 := by field_simp; norm_num
  · have hkr : (k : ℝ) ≤ 48 := by exact_mod_cast (show k ≤ 48 by omega)
    have hsq : (k : ℝ) ^ 2 ≤ (48 : ℝ) ^ 2 := by nlinarith
    have hden : 6400 * (k : ℝ) ^ 2 ≤ 2048 * (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have h := one_div_le_one_div_of_le (by positivity : 0 < 6400 * (k : ℝ) ^ 2) hden
    calc
      _ ≤ 1 / (6400 * (k : ℝ) ^ 2) := h
      _ = 1 / (1600 * (k : ℝ) ^ 2) / 4 := by field_simp; norm_num

theorem middle_block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (ht : (heightThreshold n : ℝ) ≤ s.im)
    (hlo : s.im ^ (2 / (n : ℝ)) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhi : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)) : ‖block s j‖ ≤ 8 := by
  obtain ⟨k, M, hk, hkn, hkr, hMX, hXM, hkt, htk⟩ :=
    exists_window_parameters n (2 ^ j) (by omega) ht hlo hhi
  have hσ := (line_bounds n).1.trans hline
  have h := VinogradovShortDyadic.dyadic_block_bound k M j hk (by nlinarith) hMX hXM s
    (by linarith) hkt htk
  have hsaving := saving_ge hn hk hkn
  have hdelta := delta_pos n
  have hlead : 1 - s.re - VinogradovShortResonance.saving k / 4 ≤ 0 := by
    dsimp only [line] at hline
    linarith
  have hX : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hX hlead
  have hp' := Real.rpow_le_one_of_one_le_of_nonpos hX (show 1 / 2 - s.re ≤ 0 by linarith)
  linarith

theorem block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ} (hline : line n ≤ s.re)
    (ht : (heightThreshold n : ℝ) ≤ s.im)
    (hX : ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im) :
    ‖block s j‖ ≤ 512 * s.im ^ growth n := by
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht1 : 1 ≤ s.im := by linarith
  have htpos : 0 < s.im := by linarith
  have hσ : 0 ≤ s.re := by linarith [(line_bounds n).1]
  have hXone : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hg : 1 ≤ s.im ^ growth n := Real.one_le_rpow ht1 (growth_pos (by omega : 1 ≤ n)).le
  by_cases hx : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / (n : ℝ))
  · have h := ZetaDyadicPowerBound.trivial_block_bound hσ j
    have he : ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) =
        ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
    rw [he] at h
    have hdelta : 1 - s.re ≤ delta n := by dsimp only [line] at hline; linarith
    have hdamp := Real.rpow_le_rpow_of_exponent_le hXone hdelta
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
      hx (delta_pos n).le
    rw [← Real.rpow_mul htpos.le, show 2 / (n : ℝ) * delta n = growth n by
      unfold growth; ring] at hp
    exact ((h.trans hdamp).trans hp).trans (by nlinarith)
  · by_cases hx' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)
    · exact (middle_block_bound n j hn hline ht (lt_of_not_ge hx).le hx').trans (by nlinarith)
    · by_cases hx'' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (1 / 3 : ℝ)
      · have h := DirichletBlockPowerProfile.bound 4 j hσ htpos
        have hp := VinogradovLongBlocks.sixth_profile_le (delta_pos n).le (delta_le n)
          ht1 (lt_of_not_ge hx').le hx''
        have hm := VinogradovLongBlocks.profile_antitone_sigma 4 htpos.le hXone hline
        exact ((h.trans hm).trans hp).trans (by nlinarith)
      · have h := DirichletBlockPowerProfile.bound 2 j hσ htpos
        have hp := VinogradovLongBlocks.fourth_profile_le (delta_pos n).le (delta_le n)
          ht1 (lt_of_not_ge hx'').le hX
        have hm := VinogradovLongBlocks.profile_antitone_sigma 2 htpos.le hXone hline
        exact ((h.trans hm).trans hp).trans (by nlinarith)

end
end RiemannGaussian.VinogradovSharperBudget
