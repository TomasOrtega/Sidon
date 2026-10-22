/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalCanonical
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalDiscBounds
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalLogDerivative
import Sidon.NumberTheory.RiemannGaussian.ZetaSignedPoleControl

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem localZetaPoleSum_re_eq (y : ℝ) (z : ℂ) :
    (localZetaPoleSum y z).re =
      ∑ᶠ i, (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℝ) *
        (1 / (z - i)).re := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have ht : (fun i ↦ d i • (1 / (z - i))).HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [hdi]))
  change Complex.reAddGroupHom (∑ᶠ i, d i • (1 / (z - i))) = _
  rw [map_finsum Complex.reAddGroupHom ht]
  apply finsum_congr
  intro i
  simp [d, zsmul_eq_mul]

theorem localZetaPoleSum_term_nonneg (y : ℝ) {x : ℝ} (hx : 0 < x) (i : ℂ) :
    0 ≤ (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℝ) *
      (1 / (((x - 1 / 2 : ℝ) : ℂ) - i)).re := by
  let d : ℤ := divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  by_cases hi : d = 0
  · change 0 ≤ (d : ℝ) * _
    simp [hi]
  · have hri := localZetaDivisor_re_lt_neg_half y hi
    have hre : 0 ≤ (((x - 1 / 2 : ℝ) : ℂ) - i).re := by simp; linarith
    apply mul_nonneg
    · exact_mod_cast ((analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall).divisor_nonneg i
    · rw [one_div, Complex.inv_re]
      exact div_nonneg hre (Complex.normSq_nonneg _)

theorem localZetaPoleSum_re_nonneg (y : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  rw [localZetaPoleSum_re_eq]
  exact finsum_nonneg (localZetaPoleSum_term_nonneg y hx)

theorem neg_logDeriv_riemannZeta_eq_local (y : ℝ) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    -logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y) =
      1 / ((x : ℂ) + I * y) - localZetaLogRemainder y ((x - 1 / 2 : ℝ) : ℂ) -
        localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ) := by
  let s : ℂ := ((1 + x : ℝ) : ℂ) + I * y
  let z : ℂ := ((x - 1 / 2 : ℝ) : ℂ)
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have he : 3 / 2 + I * (y : ℂ) + z = s := by dsimp [z, s]; push_cast; ring
  have hnorm : ‖z‖ ≤ 1 / 2 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hmem : z ∈ ball 0 (localZetaCanonicalRadius y) := by
    rw [mem_ball, dist_zero_right]
    linarith [(localZetaCanonicalRadius_spec y).1]
  have hf : localZetaPoleRemoved y z ≠ 0 := by
    rw [localZetaPoleRemoved, he]
    exact riemannZeta₁_ne_zero_of_one_le_re hs.le
  have hlog : logDeriv riemannZeta₁ s = localZetaLogRemainder y z + localZetaPoleSum y z := by
    rw [← he, ← logDeriv_localZetaPoleRemoved_eq]
    exact logDeriv_localZetaPoleRemoved_eq_remainder_add_poleSum y hmem hf
  have hp : s - 1 = (x : ℂ) + I * y := by dsimp [s]; push_cast; ring
  change -logDeriv riemannZeta s = _
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 (riemannZeta_ne_zero_of_one_le_re hs.le), hlog, hp]
  ring

end

end RiemannGaussian
