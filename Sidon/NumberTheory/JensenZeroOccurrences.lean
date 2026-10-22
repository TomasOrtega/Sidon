import Sidon.NumberTheory.JensenDensityGeometry
import Sidon.NumberTheory.JensenMollifier
import Sidon.NumberTheory.ZetaZeroCount

/-! # Actual zero occurrences in the mollifier's Jensen sum -/

noncomputable section

open Set MeasureTheory MeromorphicOn Metric Real

namespace Sidon

theorem jensen_detector_summand_nonneg (N : ℕ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ)) (z : ℂ) :
    0 ≤ (divisor (mollifierDetector N) (closedBall c |R|) z : ℝ) *
      Real.log (R * ‖c - z‖⁻¹) := by
  have hd : AnalyticOnNhd ℂ (mollifierDetector N) (closedBall c |R|) :=
    fun w hw => analyticAt_mollifierDetector N (hdisc w hw)
  by_cases hz : z ∈ closedBall c |R|
  · have hdiv : (0 : ℝ) ≤ divisor (mollifierDetector N) (closedBall c |R|) z := by
      exact_mod_cast hd.divisor_nonneg z
    by_cases hzero : ‖c - z‖ = 0
    · simp [hzero]
    · have hnorm : 0 < ‖c - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      have hbound : ‖c - z‖ ≤ R := by
        simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hz
      apply mul_nonneg hdiv
      rw [← div_eq_mul_inv]
      exact Real.log_nonneg ((one_le_div hnorm).mpr hbound)
  · simp [hz]

theorem zeta_jensen_weight_le_detector_summand (N : ℕ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    (analyticOrderNatAt riemannZeta ρ : ℝ) * jensenVerticalWeight R ρ y ≤
      (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) *
        Real.log (R * ‖jensenCenter y - ρ‖⁻¹) := by
  have hd : 0 < ‖jensenCenter y - ρ‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hρ y)
  by_cases hnorm : ‖jensenCenter y - ρ‖ ≤ R
  · have hmem : ρ ∈ closedBall (jensenCenter y) |R| := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hnorm
    have hζ : AnalyticOnNhd ℂ riemannZeta (closedBall (jensenCenter y) |R|) :=
      fun z hz => analyticOn_riemannZeta z (hdisc z hz)
    have horder : divisor riemannZeta (closedBall (jensenCenter y) |R|) ρ =
        (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      rw [hζ.divisor_apply hmem, ← Nat.cast_analyticOrderNatAt
        (analyticOrderAt_riemannZeta_ne_top ρ)]
      simp
    have hdom := zeta_divisor_le_mollifierDetector N hdisc hc ρ
    rw [horder] at hdom
    have hdomR : (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) := by
      exact_mod_cast hdom
    have hlog : 0 ≤ Real.log (R / ‖jensenCenter y - ρ‖) :=
      Real.log_nonneg ((one_le_div hd).mpr hnorm)
    have hw : jensenVerticalWeight R ρ y = Real.log (R / ‖jensenCenter y - ρ‖) := by
      rw [jensenVerticalWeight, ← Real.log_div hR.ne' hd.ne', max_eq_right hlog]
    rw [hw, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hdomR hlog
  · have hnot : ρ ∉ closedBall (jensenCenter y) |R| := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hnorm
    have hlog : Real.log R - Real.log ‖jensenCenter y - ρ‖ ≤ 0 := by
      have hh := Real.log_le_log hR (le_of_lt (lt_of_not_ge hnorm))
      linarith
    simp [jensenVerticalWeight, max_eq_left hlog, hnot]

theorem sum_zeta_jensen_weight_le_detector (N : ℕ) (T : ℝ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) :
    (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤
      ∑ᶠ ρ, (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) *
        Real.log (R * ‖jensenCenter y - ρ‖⁻¹) := by
  classical
  let D := divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|)
  let q : ℂ → ℝ := fun ρ => (D ρ : ℝ) * Real.log (R * ‖jensenCenter y - ρ‖⁻¹)
  let U := criticalZetaZeros T ∪ (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hsupport : Function.support q ⊆ (U : Set ℂ) := by
    intro ρ hρ
    apply Finset.mem_union_right
    have hdρ : ρ ∈ D.support := by
      change D ρ ≠ 0
      intro hzero
      exact hρ (by simp [q, hzero])
    simpa only [Set.Finite.mem_toFinset] using hdρ
  change (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤ ∑ᶠ ρ, q ρ
  rw [sum_zetaZeroOccurrences T (fun ρ => jensenVerticalWeight R ρ y),
    finsum_eq_finsetSum_of_support_subset q hsupport]
  calc
    _ ≤ ∑ ρ ∈ criticalZetaZeros T, q ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact zeta_jensen_weight_le_detector_summand N hR hdisc hc
        (mem_criticalZetaZeros.mp hρ).2.2.1
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro ρ _ _
      exact jensen_detector_summand_nonneg N hR hdisc ρ

theorem sum_zeta_jensen_weight_le_error (N : ℕ) (T : ℝ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) :
    (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤
      circleAverage (fun z => ‖mollifierError N z‖ ^ 2) (jensenCenter y) R -
        Real.log ‖mollifierDetector N (jensenCenter y)‖ :=
  (sum_zeta_jensen_weight_le_detector N T hR hdisc hc).trans
    (jensen_mollifier_detector_le N hR.ne' hdisc hc)

end Sidon
