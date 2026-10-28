module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativeRecursionBudget
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
public import Sidon.NumberTheory.RiemannGaussian.ZetaSignedExactPole
public import Sidon.NumberTheory.RiemannGaussian.ZetaSignedPrimeSeries
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovAngularBound
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCanonical

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovAngularBudget
noncomputable section
open Complex Metric Set
open RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection RiemannGaussian.ZetaVinogradovCanonical
open RiemannGaussian.ZetaNearOneLocalDisc (center)
open RiemannGaussian.ZetaNearOneCanonical (translated)
open RiemannGaussian.ZetaNearOneSignedBound (coupledSum coupledSum_nonneg source_le_sum)
def budget (n : ℕ) (x t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 + (8 * allowance n x t + 2 * allowance n x (2 * t)) / (Real.pi * delta n)

theorem source_le_budget (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta n / 4) (hnear : x + 1 - ρ.1.re < delta n) :
    4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta n) ^ 2) ≤
      3 / x + budget n x ρ.1.im := by
  have hsmall : x ≤ 1 / 4 := by linarith [delta_le n]
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1 + x) (by linarith) ρ.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hsmall
  have hzero := ZetaVinogradovAngularBound.neg_logDeriv_re_le_sub_zero n hn ρ ht hx hx' hnear
  have ht2 : (heightThreshold n : ℝ) + 1 ≤ |2 * ρ.1.im| := by
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg ρ.1.im]
  have hdouble := ZetaVinogradovAngularBound.neg_logDeriv_re_le n hn ht2 hx hx'
  change 0 ≤ 3 * (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re +
    4 * (-logDeriv riemannZeta (center x ρ.1.im)).re +
    (-logDeriv riemannZeta (center x (2 * ρ.1.im))).re at hprime
  unfold budget
  simp only [div_eq_mul_inv] at hreal hzero hdouble ⊢
  nlinarith

theorem margin_of_budget (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|) {d : ℝ} (hd : 0 < d)
    (hdsmall : d < delta n / 28)
    (hpay : 14 * d * budget n (6 * d) ρ.1.im + 392 * d ^ 2 / (delta n) ^ 2 < 1) :
    d < 1 - ρ.1.re := by
  by_contra! hgap
  have hδ := delta_pos n
  let v := 6 * d + 1 - ρ.1.re
  have hv : 0 < v := by dsimp only [v]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hvup : v ≤ 7 * d := by dsimp only [v]; linarith
  have hsource := source_le_budget n hn ρ ht (by positivity : 0 < 6 * d)
    (by linarith : 6 * d ≤ delta n / 4)
    (by linarith : 6 * d + 1 - ρ.1.re < delta n)
  have hinv : 1 / (7 * d) ≤ 1 / v := one_div_le_one_div_of_le hv hvup
  have hcorr : v / (delta n) ^ 2 ≤ 7 * d / (delta n) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hbase : 0 ≤ 1 / (7 * d) - 7 * d / (delta n) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < (delta n) ^ 2)
      (by positivity : 0 < 7 * d)).mpr
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 28 * d) hδ.le).mpr
      (by linarith : 28 * d ≤ delta n)
    nlinarith
  have hmult : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hlower : 1 / (7 * d) - 7 * d / (delta n) ^ 2 ≤
      (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / v - v / (delta n) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hmult hbase
    have h' := mul_le_mul_of_nonneg_left (show 1 / (7 * d) - 7 * d / (delta n) ^ 2 ≤
      1 / v - v / (delta n) ^ 2 by linarith)
      (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
    linarith
  have hs : 4 * (1 / (7 * d) - 7 * d / (delta n) ^ 2) ≤
      3 / (6 * d) + budget n (6 * d) ρ.1.im := by
    change 4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / v - v / (delta n) ^ 2) ≤ _ at hsource
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 14 * d)
  have hleft : 14 * d * (4 * (1 / (7 * d) - 7 * d / (delta n) ^ 2)) =
      8 - 392 * d ^ 2 / (delta n) ^ 2 := by field_simp; ring
  have hright : 14 * d * (3 / (6 * d) + budget n (6 * d) ρ.1.im) =
      7 + 14 * d * budget n (6 * d) ρ.1.im := by field_simp; ring
  rw [hleft, hright] at hm
  linarith

end
end RiemannGaussian.ZetaVinogradovAngularBudget
