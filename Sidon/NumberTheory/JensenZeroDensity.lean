import Sidon.NumberTheory.JensenZeroOccurrences
import Sidon.NumberTheory.CircleAverageVertical
import Sidon.NumberTheory.MollifierCenter

/-! # Integrated Jensen counting for the actual zeta zeros -/

noncomputable section

open Set MeasureTheory Metric Real

namespace Sidon

theorem jensen_disc_avoids_pole {R y : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2)
    (hy : 3 ≤ y) : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ) := by
  intro z hz he
  subst z
  have hh : ‖jensenCenter y - 1‖ ≤ R := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_nonneg hR] using hz
  have him := Complex.abs_im_le_norm (jensenCenter y - 1)
  have hi : (jensenCenter y - 1).im = y := by simp [jensenCenter]
  rw [hi] at him
  have hh' := (le_abs_self y).trans him
  linarith

theorem continuousOn_mollifierError_sq_rectangle (N : ℕ) (R T : ℝ) :
    ContinuousOn (fun z => ‖mollifierError N z‖ ^ 2) (verticalCircleRectangle R T) := by
  intro z hz
  have hz1 : z ≠ (1 : ℂ) := by
    intro he
    subst z
    have hh := hz.2.1
    norm_num at hh
  exact ((analyticAt_mollifierError N hz1).continuousAt.norm.pow 2).continuousWithinAt

theorem jensen_zero_occurrences_bound {N : ℕ} (hN : 131072 ≤ N)
    {σ δ T L : ℝ} (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hT : 3 ≤ T)
    (S : Finset (ℂ × ℕ)) (hS : S ⊆ zetaZeroOccurrences T)
    (hβ : ∀ z ∈ S, σ + δ ≤ z.1.re) (hγ : ∀ z ∈ S, 4 ≤ z.1.im)
    (hslice : ∀ u ∈ Icc σ (4 - σ),
      (∫ t in Icc 1 (T + 3), ‖mollifierError N ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ L) :
    (S.card : ℝ) * (2 * δ ^ 2 / 3) ≤ L + (T - 2) * (131072 / (N : ℝ)) := by
  let R : ℝ := 2 - σ
  let C : ℝ := 131072 / (N : ℝ)
  let F : ℂ → ℝ := fun z => ‖mollifierError N z‖ ^ 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R ≤ 3 / 2 := by dsimp [R]; linarith
  have hY : (3 : ℝ) ≤ T + 1 := by linarith
  have hF : ContinuousOn F (verticalCircleRectangle R T) :=
    continuousOn_mollifierError_sq_rectangle N R T
  have hiF := integrableOn_circleAverage_vertical hR.le hR1 hF
  have hiC : IntegrableOn (fun _ : ℝ => C) (Icc 3 (T + 1)) := integrable_const _
  have hws : Continuous (fun y : ℝ => ∑ z ∈ S, jensenVerticalWeight R z.1 y) := by
    apply continuous_finsetSum
    intro z hz
    exact continuous_jensenVerticalWeight R (zetaZeroOccurrences_re_bounds (hS hz)).2
  have hcount := card_mul_jensen_mass_le_integral S Prod.fst hσ0 hσ1 hδ0 hδ1 hβ
    (fun z hz => (zetaZeroOccurrences_re_bounds (hS hz)).2) hγ
    (fun z hz => (zetaZeroOccurrences_height_bounds (hS hz)).2)
  rw [intervalIntegral.integral_of_le hY, ← integral_Icc_eq_integral_Ioc] at hcount
  have hpoint (y : ℝ) (hy : y ∈ Icc 3 (T + 1)) :
      (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
        circleAverage F (2 + (y : ℂ) * Complex.I) R + C := by
    have hc := mollifierDetector_center_bound hN (s := jensenCenter y)
      (by simp [jensenCenter])
    have hh := sum_zeta_jensen_weight_le_error N T hR
      (jensen_disc_avoids_pole hR.le hR1 hy.1) hc.1
    have hsubsum : (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
        ∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun z _ _ => le_max_left 0 _)
    have hc' : -Real.log ‖mollifierDetector N (jensenCenter y)‖ ≤ C := hc.2
    change (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
      circleAverage F (jensenCenter y) R + C
    exact hsubsum.trans (hh.trans (by dsimp [F]; linarith))
  have hcircle : (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R) ≤ L := by
    apply integral_circleAverage_vertical_le hR.le hR1 hT hF
      (fun z _ => sq_nonneg _)
    intro u hu
    apply hslice u
    simpa only [R, sub_sub_cancel, show (2 : ℝ) + (2 - σ) = 4 - σ by ring] using hu
  have hconst : (∫ _ in Icc (3 : ℝ) (T + 1), C) = (T - 2) * C := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  calc
    _ ≤ ∫ y in Icc 3 (T + 1), ∑ z ∈ S, jensenVerticalWeight R z.1 y := hcount
    _ ≤ ∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R + C :=
      setIntegral_mono_on (hws.continuousOn.integrableOn_compact isCompact_Icc)
        (hiF.add hiC) measurableSet_Icc hpoint
    _ = (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R) +
        (T - 2) * C := by rw [integral_add hiF hiC, hconst]
    _ ≤ _ := by dsimp [C]; linarith

end Sidon
