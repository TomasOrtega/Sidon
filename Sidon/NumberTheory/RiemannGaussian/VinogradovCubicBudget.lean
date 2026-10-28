module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
public import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovLongBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortDyadic
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortResonance
public import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound

@[expose] public section

namespace RiemannGaussian.VinogradovCubicBudget
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovSharperBudget (delta line delta_pos delta_le line_bounds)
def growth (n : ℕ) : ℝ := 40 * delta n * Real.sqrt (delta n)

theorem sqrt_delta (n : ℕ) :
    Real.sqrt (delta n) = 1 / (64 * (2 * (n : ℝ) + 1)) := by
  apply (Real.sqrt_eq_iff_eq_sq (delta_pos n).le (by positivity)).mpr
  unfold delta
  field_simp
  ring

theorem growth_pos (n : ℕ) : 0 < growth n := by
  unfold growth
  positivity [delta_pos n]

theorem growth_eq (n : ℕ) :
    growth n = 5 / (32768 * (2 * (n : ℝ) + 1) ^ 3) := by
  rw [growth, sqrt_delta]
  unfold delta
  field_simp
  ring

theorem small_rate_le {n : ℕ} (hn : 2 ≤ n) :
    (2 / (8 * (n : ℝ))) * delta n ≤ growth n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 2 / (8 * (n : ℝ)) ≤ 40 / (64 * (2 * (n : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have h := mul_le_mul_of_nonneg_right hc (delta_pos n).le
  simpa only [growth, sqrt_delta, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using h

theorem middle_block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (ht : (heightThreshold (8 * n) : ℝ) ≤ s.im)
    (hlo : s.im ^ (2 / (8 * (n : ℝ))) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhi : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)) :
    ‖block s j‖ ≤ 8 * s.im ^ growth n := by
  have hlo' : s.im ^ (2 / ((8 * n : ℕ) : ℝ)) ≤ ((2 ^ j : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlo
  obtain ⟨k, M, hk, _, hkr, hMX, hXM, hkt, htk⟩ :=
    exists_window_parameters (8 * n) (2 ^ j) (by omega) ht hlo' hhi
  have hσ := (line_bounds n).1.trans hline
  have h := VinogradovShortDyadic.dyadic_block_bound k M j hk (by nlinarith) hMX hXM s
    (by linarith) hkt htk
  have hXNat : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by omega)
  have hX : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hXNat
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen _
  have ht1 : 1 < s.im := by linarith
  have hg : 1 ≤ s.im ^ growth n := Real.one_le_rpow ht1.le (growth_pos n).le
  have hp' := Real.rpow_le_one_of_one_le_of_nonpos hX (show 1 / 2 - s.re ≤ 0 by linarith)
  by_cases hk48 : 48 ≤ k
  · have hdamp : 1 - s.re ≤ delta n := by dsimp only [line] at hline; linarith
    have hp := VinogradovCubicSaving.power_le hk48 (by nlinarith : 16 ≤ M) hXM hXNat
      ht1 hkt (delta_pos n).le hdamp
    change ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re - VinogradovShortResonance.saving k / 4) ≤
      s.im ^ growth n at hp
    nlinarith
  · have hsaving := VinogradovSharperBudget.saving_ge hn hk (by omega : k ≤ 2 * n + 1)
    have hlead : 1 - s.re - VinogradovShortResonance.saving k / 4 ≤ 0 := by
      dsimp only [line] at hline
      linarith [delta_pos n]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hX hlead
    nlinarith

theorem block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ} (hline : line n ≤ s.re)
    (ht : (heightThreshold (8 * n) : ℝ) ≤ s.im)
    (hX : ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im) :
    ‖block s j‖ ≤ 512 * s.im ^ growth n := by
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen _
  have ht1 : 1 ≤ s.im := by linarith
  have htpos : 0 < s.im := by linarith
  have hσ : 0 ≤ s.re := by linarith [(line_bounds n).1]
  have hXone : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hg : 1 ≤ s.im ^ growth n := Real.one_le_rpow ht1 (growth_pos n).le
  by_cases hx : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / (8 * (n : ℝ)))
  · have h := ZetaDyadicPowerBound.trivial_block_bound hσ j
    have he : ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) =
        ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
    rw [he] at h
    have hdelta : 1 - s.re ≤ delta n := by dsimp only [line] at hline; linarith
    have hdamp := Real.rpow_le_rpow_of_exponent_le hXone hdelta
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
      hx (delta_pos n).le
    rw [← Real.rpow_mul htpos.le] at hp
    have hrate := Real.rpow_le_rpow_of_exponent_le ht1 (small_rate_le (by omega : 2 ≤ n))
    exact (((h.trans hdamp).trans hp).trans hrate).trans (by nlinarith)
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
end RiemannGaussian.VinogradovCubicBudget
