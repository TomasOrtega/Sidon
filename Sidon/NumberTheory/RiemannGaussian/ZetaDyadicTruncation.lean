/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Data.Nat.Log
import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
import Sidon.NumberTheory.RiemannGaussian.EtaUniformTailBound
import Sidon.NumberTheory.RiemannGaussian.EtaZetaPoleBounds
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram

namespace RiemannGaussian.ZetaDyadicTruncation
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks
def etaFactor (s : ℂ) : ℂ := 1 - 2 * zetaPrimeFeature s 2

def remainder (s : ℂ) (J : ℕ) : ℂ := pairedEtaCore s - pairedEtaCorePartialSum (2 ^ J) s

def depth (s : ℂ) : ℕ := Nat.log 2 (⌈‖s‖⌉₊ + 1)

theorem factor_eq (s : ℂ) : etaFactor s = 1 - 2 * (2 : ℂ) ^ (-s) := by
  rw [etaFactor, feature_eq_cpow s (by norm_num)]
  norm_num only [Nat.cast_ofNat]

theorem reconstruction {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (J : ℕ) :
    etaFactor s * riemannZeta s =
      (∑ j ∈ Finset.range (J + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
          zetaPrimeFeature s (2 ^ (J + 1)) + remainder s J := by
  rw [factor_eq, ← pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
    ← eta_pow_two_eq_blocks, remainder]
  ring

theorem remainder_bound {s : ℂ} (hs : 0 < s.re) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖remainder s J‖ ≤ 2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re)) :=
  norm_pairedEtaCore_tail_le_two hs (2 ^ J) hscale

theorem factor_lower (s : ℂ) : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖etaFactor s‖ := by
  have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
  rw [norm_two_mul_two_cpow_neg, norm_one, norm_sub_rev, ← factor_eq] at h
  exact h

theorem factor_lower_pos {s : ℂ} (hs : s.re < 1) : 0 < (2 : ℝ) ^ (1 - s.re) - 1 := by
  have h : 1 < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
  linarith

theorem zeta_norm_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤
      (‖(∑ j ∈ Finset.range (J + 1), block s j) -
          2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
            zetaPrimeFeature s (2 ^ (J + 1))‖ +
        2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re))) /
          ((2 : ℝ) ^ (1 - s.re) - 1) := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  have he := congrArg norm (reconstruction hs hne J)
  rw [norm_mul] at he
  have hu := (norm_add_le
    ((∑ j ∈ Finset.range (J + 1), block s j) -
      2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
        zetaPrimeFeature s (2 ^ (J + 1))) (remainder s J)).trans
    (add_le_add le_rfl (remainder_bound hs J hscale))
  rw [← he] at hu
  have hl := mul_le_mul_of_nonneg_right (factor_lower s) (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (factor_lower_pos hs1)).mpr
  nlinarith

theorem depth_scale (s : ℂ) : ‖s‖ ≤ ((2 * 2 ^ depth s + 1 : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  rw [Nat.succ_eq_add_one, pow_succ] at hp
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 : ℕ) ^ depth s * 2 : ℕ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  nlinarith

theorem depth_length_lt (s : ℂ) : ((2 ^ depth s : ℕ) : ℝ) < ‖s‖ + 2 := by
  have hp := Nat.pow_log_le_self 2 (show ⌈‖s‖⌉₊ + 1 ≠ 0 by omega)
  have hr : ((2 ^ depth s : ℕ) : ℝ) ≤ ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (norm_nonneg s)
  push_cast at hr ⊢
  linarith

theorem depth_le_log (s : ℂ) : (depth s : ℝ) ≤ Real.log (‖s‖ + 2) / Real.log 2 := by
  have hp : (2 : ℝ) ^ depth s ≤ ‖s‖ + 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (depth_length_lt s).le
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth s) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

end
end RiemannGaussian.ZetaDyadicTruncation
