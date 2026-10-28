module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.GaussianSpectral
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiDivisorContour
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiInverseSquareSummability
public import Sidon.NumberTheory.RiemannGaussian.GaussianXiLogDerivativeGrowth
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiCanonicalCauchy
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiCanonicalLogVariation

@[expose] public section

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

def riemannXiCanonicalZeroWindow (n : ℕ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow (xiCanonicalRadius n)).filter
    (fun rho => ‖(rho.1 : ℂ)‖ < xiCanonicalRadius n)

@[simp] theorem mem_riemannXiCanonicalZeroWindow (n : ℕ) (rho : NontrivialZetaZero) :
    rho ∈ riemannXiCanonicalZeroWindow n ↔ ‖(rho.1 : ℂ)‖ < xiCanonicalRadius n := by
  classical
  rw [riemannXiCanonicalZeroWindow, Finset.mem_filter,
    mem_spectralZetaZeroWindow (xiCanonicalRadius_pos n).le]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rw [zetaSpectralCoordinate_re]
  exact (Complex.abs_im_le_norm _).trans h.le

theorem tendsto_riemannXiCanonicalZeroWindow_atTop :
    Tendsto riemannXiCanonicalZeroWindow atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro S
  filter_upwards [tendsto_xiCanonicalRadius_atTop.eventually
    (eventually_gt_atTop (∑ rho ∈ S, ‖(rho.1 : ℂ)‖))] with n hn
  intro rho hrho
  rw [mem_riemannXiCanonicalZeroWindow]
  exact (Finset.single_le_sum (fun sigma _ => norm_nonneg (sigma.1 : ℂ)) hrho).trans_lt hn

theorem divisor_riemannXi_ball_at_zetaZero {R : ℝ} (rho : NontrivialZetaZero)
    (hrho : ‖(rho.1 : ℂ)‖ < R) :
    divisor riemannXi (ball 0 R) rho.1 = (analyticZetaZeroMultiplicity rho : ℤ) := by
  have hmem : (rho.1 : ℂ) ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using hrho
  rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_apply hmem,
    analyticOrderAt_riemannXi_eq_riemannZeta,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)]
  simp [analyticZetaZeroMultiplicity]

def zetaLogDerivDifferenceSummand (s w : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) * (1 / (s - rho.1) - 1 / (w - rho.1))

theorem riemannXiCanonicalCauchyDifference_eq_zeroWindow (n : ℕ) (s w : ℂ) :
    riemannXiCanonicalCauchyDifference n s w =
      ∑ rho ∈ riemannXiCanonicalZeroWindow n, zetaLogDerivDifferenceSummand s w rho := by
  classical
  let W := riemannXiCanonicalZeroWindow n
  let S : Finset ℂ := W.image (fun rho => (rho.1 : ℂ))
  have hsupport : Function.support (fun i =>
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
        (1 / (s - i) - 1 / (w - i))) ⊆ S := by
    intro i hi
    have hdi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 := by
      intro hzero
      exact hi (by simp [hzero])
    have hxi := riemannXi_eq_zero_of_divisor_ball_ne_zero hdi
    let rho : NontrivialZetaZero :=
      ⟨i, (riemannXi_eq_zero_iff_isNontrivialZetaZero i).mp hxi⟩
    apply Finset.mem_image.mpr
    refine ⟨rho, ?_, rfl⟩
    apply (mem_riemannXiCanonicalZeroWindow n rho).mpr
    simpa only [mem_ball, dist_zero_right] using
      (divisor riemannXi (ball 0 (xiCanonicalRadius n))).supportWithinDomain hdi
  unfold riemannXiCanonicalCauchyDifference
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  change (∑ i ∈ W.image (fun rho => (rho.1 : ℂ)), _) = _
  rw [Finset.sum_image (fun rho _ sigma _ heq => Subtype.ext heq)]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [divisor_riemannXi_ball_at_zetaZero rho
    ((mem_riemannXiCanonicalZeroWindow n rho).mp hrho)]
  simp [zetaLogDerivDifferenceSummand, zsmul_eq_mul]

private lemma bounded_zetaZero_norm_finite (B : ℝ) :
    {rho : NontrivialZetaZero | ‖(rho.1 : ℂ)‖ ≤ B}.Finite := by
  apply (spectralZetaZeroWindow (max B 0)).finite_toSet.subset
  intro rho hrho
  apply (mem_spectralZetaZeroWindow (le_max_right B 0) rho).mpr
  rw [zetaSpectralCoordinate_re]
  exact (Complex.abs_im_le_norm _).trans (hrho.trans (le_max_left _ _))

private lemma cauchy_difference_norm_le {s w i : ℂ}
    (hs : 2 * ‖s‖ < ‖i‖) (hw : 2 * ‖w‖ < ‖i‖) (hi : 1 < ‖i‖) :
    ‖1 / (s - i) - 1 / (w - i)‖ ≤ 8 * ‖s - w‖ / (1 + ‖i‖ ^ 2) := by
  have hsi : ‖i‖ / 2 ≤ ‖s - i‖ := by
    have := norm_sub_norm_le i s
    rw [norm_sub_rev i s] at this
    linarith
  have hwi : ‖i‖ / 2 ≤ ‖w - i‖ := by
    have := norm_sub_norm_le i w
    rw [norm_sub_rev i w] at this
    linarith
  have hds : s - i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hsi)
  have hdw : w - i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hwi)
  have hid : 1 / (s - i) - 1 / (w - i) = (w - s) / ((s - i) * (w - i)) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, norm_sub_rev w s]
  calc
    ‖s - w‖ / (‖s - i‖ * ‖w - i‖)
      ≤ ‖s - w‖ / ((‖i‖ / 2) * (‖i‖ / 2)) := by gcongr
    _ = 4 * ‖s - w‖ / ‖i‖ ^ 2 := by field_simp; ring
    _ ≤ 8 * ‖s - w‖ / (1 + ‖i‖ ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hi2 : 1 ≤ ‖i‖ ^ 2 := by nlinarith
      nlinarith [mul_nonneg (norm_nonneg (s - w)) (sub_nonneg.mpr hi2)]

theorem summable_zetaLogDerivDifferenceSummand (s w : ℂ) :
    Summable (zetaLogDerivDifferenceSummand s w) := by
  have hsum := summable_distinct_zetaZeroInverseSquareNorm.mul_left (8 * ‖s - w‖)
  apply hsum.of_norm_bounded_eventually
  filter_upwards [(bounded_zetaZero_norm_finite (1 + 2 * ‖s‖ + 2 * ‖w‖)).eventually_cofinite_notMem]
    with rho hrho
  have hr : 1 + 2 * ‖s‖ + 2 * ‖w‖ < ‖(rho.1 : ℂ)‖ := by simpa using hrho
  have hnorm := cauchy_difference_norm_le (s := s) (w := w) (i := rho.1)
    (by linarith [norm_nonneg w]) (by linarith [norm_nonneg s])
    (by linarith [norm_nonneg s, norm_nonneg w])
  rw [zetaLogDerivDifferenceSummand, norm_mul, Complex.norm_natCast]
  calc
    (analyticZetaZeroMultiplicity rho : ℝ) * ‖1 / (s - rho.1) - 1 / (w - rho.1)‖
      ≤ (analyticZetaZeroMultiplicity rho : ℝ) *
          (8 * ‖s - w‖ / (1 + ‖(rho.1 : ℂ)‖ ^ 2)) := by gcongr
    _ = 8 * ‖s - w‖ *
        ((analyticZetaZeroMultiplicity rho : ℝ) / (1 + ‖(rho.1 : ℂ)‖ ^ 2)) := by ring

theorem hasSum_zetaLogDerivDifference {s w : ℂ}
    (hs : riemannXi s ≠ 0) (hw : riemannXi w ≠ 0) :
    HasSum (zetaLogDerivDifferenceSummand s w)
      (logDeriv riemannXi s - logDeriv riemannXi w) := by
  have hsum := summable_zetaLogDerivDifferenceSummand s w
  have hfinite := hsum.hasSum.comp tendsto_riemannXiCanonicalZeroWindow_atTop
  have hcanonical := tendsto_riemannXiCanonicalCauchyDifference hs hw
  simp only [riemannXiCanonicalCauchyDifference_eq_zeroWindow] at hcanonical
  have heq := tendsto_nhds_unique hfinite hcanonical
  exact heq ▸ hsum.hasSum

theorem hasSum_zetaLogDeriv_reflection {s : ℂ} (hs : riemannXi s ≠ 0) :
    HasSum (zetaLogDerivDifferenceSummand s (1 - s)) (2 * logDeriv riemannXi s) := by
  have hreflect : riemannXi (1 - s) ≠ 0 := by simpa only [riemannXi_one_sub] using hs
  have heq : logDeriv riemannXi s - logDeriv riemannXi (1 - s) =
      2 * logDeriv riemannXi s := by
    simp only [logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
    ring
  simpa only [heq] using hasSum_zetaLogDerivDifference hs hreflect

theorem zetaLogDerivDifferenceSummand_reflection_re (s : ℂ) (rho : NontrivialZetaZero) :
    (zetaLogDerivDifferenceSummand s (1 - s) rho).re =
      (analyticZetaZeroMultiplicity rho : ℝ) *
        ((s.re - rho.1.re) / Complex.normSq (s - rho.1) +
          (s.re + rho.1.re - 1) / Complex.normSq (1 - s - rho.1)) := by
  simp only [zetaLogDerivDifferenceSummand, mul_re, natCast_re, natCast_im,
    zero_mul, sub_zero, sub_re, one_div, inv_re, one_re]
  ring

end

end RiemannGaussian
