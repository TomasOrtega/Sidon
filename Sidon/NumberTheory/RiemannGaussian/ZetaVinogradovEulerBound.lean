/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
import Sidon.NumberTheory.RiemannGaussian.ZetaEulerLineBound
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLineBudget
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovBound

namespace RiemannGaussian.ZetaVinogradovEulerBound
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.ZetaDyadicTruncation
open RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection
open scoped ComplexConjugate

theorem bound_strip (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : (heightThreshold n : ℝ) ≤ s.im) :
    ‖riemannZeta s‖ ≤ 8192 * s.im ^ growth n * Real.log s.im := by
  have hσ : 0 < s.re := by linarith [(line_bounds n).1]
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht2 : 2 ≤ s.im := by linarith
  have hprefix : ‖positivePrefix s (2 ^ (depth s + 1))‖ ≤
      ((depth s + 1 : ℕ) : ℝ) * (512 * s.im ^ growth n) := by
    rw [prefix_pow_two]
    calc
      _ ≤ ∑ j ∈ Finset.range (depth s + 1), ‖block s j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (depth s + 1), (512 * s.im ^ growth n) := by
        apply Finset.sum_le_sum
        intro j hj
        exact canonical_block_bound n hn hline hσ1 ht
          (by have hh := Finset.mem_range.mp hj; omega)
      _ = _ := by simp
  have hc := ZetaNearOneLineBudget.canonical_count_le hσ.le hσ1 ht2
  have hp : 1 ≤ s.im ^ growth n :=
    Real.one_le_rpow (by linarith) (growth_pos (by omega : 1 ≤ n)).le
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 512 * s.im ^ growth n)
  have hprod : (1 / 2 : ℝ) ≤ s.im ^ growth n * Real.log s.im := by nlinarith
  have h := ZetaEulerLineBound.norm_le_prefix_add_six hσ hσ1 ht2
  nlinarith

theorem bound_strip_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ growth n * Real.log |s.im| := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound_strip n hn hline hσ1 ht
  · have hsneg : s.im < 0 := lt_of_not_ge hs
    have hline' : line n ≤ (conj s).re := by simpa using hline
    have hσ1' : (conj s).re ≤ 1 := by simpa using hσ1
    have ht' : (heightThreshold n : ℝ) ≤ (conj s).im := by simpa [abs_of_neg hsneg] using ht
    have h := bound_strip n hn hline' hσ1' ht'
    simpa [abs_of_neg hsneg] using h

end
end RiemannGaussian.ZetaVinogradovEulerBound
