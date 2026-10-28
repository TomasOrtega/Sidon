module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDerivativeCutoff
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerEnvelope
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.DirichletHigherDerivativeBound
public import Sidon.NumberTheory.RiemannGaussian.LogarithmicDerivativeFamily
public import Sidon.NumberTheory.RiemannGaussian.UniformDerivativePowerBound
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

@[expose] public section

namespace RiemannGaussian.UniformDirichletPowerBound
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativePowerEnvelope
open RiemannGaussian.LogarithmicDerivativeFamily
theorem ratio_amp_le_four (k : ℕ) : (ratio k) ^ amp k ≤ 4 := by
  have hg : ∀ j : ℕ, ((j + 2 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have he : ((k + 2 : ℕ) : ℝ) * amp k ≤ 2 := by
    unfold amp
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr (hg k)
  unfold ratio
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at h ⊢
  exact h

theorem feature_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      envelope k N (lowerScale s.im X k) (ratio k) * zetaPrimeExpWeight s.re a := by
  have hratio : 1 ≤ ratio k := by
    unfold ratio
    exact one_le_pow₀ (by norm_num)
  apply (DirichletHigherDerivativeBound.feature_bound cutoffs k hσ ht hX a N ha hb).trans
  exact mul_le_mul_of_nonneg_right
    (UniformDerivativePowerBound.budget_bound k N (lowerScale_pos ht hX k) hratio)
    (Real.exp_pos _).le

theorem uniform_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      32 * (4 * N * (lowerScale s.im X k) ^ alpha k +
        (N : ℝ) ^ beta k * (lowerScale s.im X k) ^ (-alpha k)) *
          zetaPrimeExpWeight s.re a := by
  apply (feature_bound k hσ ht hX a N ha hb).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  unfold envelope mainTerm errorTerm
  have hscale := lowerScale_pos ht hX k
  gcongr
  exact ratio_amp_le_four k

end
end RiemannGaussian.UniformDirichletPowerBound
