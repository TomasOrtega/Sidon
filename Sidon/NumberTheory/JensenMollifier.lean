import Sidon.NumberTheory.DirichletMollifier
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Actual analytic mollifiers in Jensen's formula -/

noncomputable section

open MeasureTheory MeromorphicOn Metric Real

namespace Sidon

/-- The balanced analytic mollifier error. -/
def mollifierError (N : ℕ) (s : ℂ) : ℂ := riemannZeta s * dirichletMollifier N s - 1

/-- This detector retains every zeta zero while being close to one at the center. -/
def mollifierDetector (N : ℕ) (s : ℂ) : ℂ := 1 - mollifierError N s ^ 2

def mollifierCompanion (N : ℕ) (s : ℂ) : ℂ :=
  dirichletMollifier N s * (2 - riemannZeta s * dirichletMollifier N s)

theorem mollifierDetector_factor (N : ℕ) (s : ℂ) :
    mollifierDetector N s = riemannZeta s * mollifierCompanion N s := by
  unfold mollifierDetector mollifierError mollifierCompanion
  ring

theorem analyticAt_mollifierError (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierError N) s := by
  have hζ := analyticOn_riemannZeta s hs
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  exact (hζ.mul hM).sub analyticAt_const

theorem analyticAt_mollifierDetector (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierDetector N) s :=
  analyticAt_const.sub ((analyticAt_mollifierError N hs).pow 2)

theorem analyticAt_mollifierCompanion (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierCompanion N) s := by
  have hζ := analyticOn_riemannZeta s hs
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  exact hM.mul (analyticAt_const.sub (hζ.mul hM))

/-- Every actual zeta multiplicity is retained by the analytic detector. -/
theorem zeta_divisor_le_mollifierDetector (N : ℕ) {c : ℂ} {R : ℝ}
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N c ≠ 0) (z : ℂ) :
    divisor riemannZeta (closedBall c |R|) z ≤
      divisor (mollifierDetector N) (closedBall c |R|) z := by
  let U := closedBall c |R|
  have hζ : AnalyticOnNhd ℂ riemannZeta U := fun z hz => analyticOn_riemannZeta z (hdisc z hz)
  have hM : AnalyticOnNhd ℂ (mollifierCompanion N) U :=
    fun z hz => analyticAt_mollifierCompanion N (hdisc z hz)
  have hcU : c ∈ U := mem_closedBall_self (abs_nonneg R)
  have hprod : riemannZeta c * mollifierCompanion N c ≠ 0 := by
    rw [← mollifierDetector_factor]
    exact hc
  have hζc : riemannZeta c ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hMc : mollifierCompanion N c ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hζfin : ∀ w ∈ U, meromorphicOrderAt riemannZeta w ≠ ⊤ := by
    intro w hw
    apply hζ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c |R|).isPreconnected hcU hw
    rw [(hζ c hcU).meromorphicOrderAt_eq, (hζ c hcU).analyticOrderAt_eq_zero.mpr hζc]
    simp
  have hMfin : ∀ w ∈ U, meromorphicOrderAt (mollifierCompanion N) w ≠ ⊤ := by
    intro w hw
    apply hM.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c |R|).isPreconnected hcU hw
    rw [(hM c hcU).meromorphicOrderAt_eq, (hM c hcU).analyticOrderAt_eq_zero.mpr hMc]
    simp
  have hdiv := divisor_fun_mul hζ.meromorphicOn hM.meromorphicOn hζfin hMfin
  have hfactor : (fun w => riemannZeta w * mollifierCompanion N w) = mollifierDetector N := by
    funext w
    exact (mollifierDetector_factor N w).symm
  rw [hfactor] at hdiv
  change divisor riemannZeta U z ≤ divisor (mollifierDetector N) U z
  rw [hdiv]
  exact le_add_of_nonneg_right (hM.divisor_nonneg z)

theorem log_norm_one_sub_sq_le (z : ℂ) : Real.log ‖1 - z ^ 2‖ ≤ ‖z‖ ^ 2 := by
  by_cases hz : ‖1 - z ^ 2‖ = 0
  · rw [hz, Real.log_zero]
    positivity
  · have hp : 0 < ‖1 - z ^ 2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hlog := Real.log_le_sub_one_of_pos hp
    have hnorm := norm_sub_le (1 : ℂ) (z ^ 2)
    rw [norm_one, norm_pow] at hnorm
    linarith

/-- The integrated Jensen method only needs the square-error circle average. -/
theorem jensen_mollifier_detector_le (N : ℕ) {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N c ≠ 0) :
    (∑ᶠ z, (divisor (mollifierDetector N) (closedBall c |R|) z : ℝ) *
      Real.log (R * ‖c - z‖⁻¹)) ≤
        circleAverage (fun z => ‖mollifierError N z‖ ^ 2) c R -
          Real.log ‖mollifierDetector N c‖ := by
  have hd : AnalyticOnNhd ℂ (mollifierDetector N) (closedBall c |R|) :=
    fun z hz => analyticAt_mollifierDetector N (hdisc z hz)
  have he : AnalyticOnNhd ℂ (mollifierError N) (closedBall c |R|) :=
    fun z hz => analyticAt_mollifierError N (hdisc z hz)
  have hlog := hd.circleAverage_log_norm hR hc
  have hmono : circleAverage (fun z => Real.log ‖mollifierDetector N z‖) c R ≤
      circleAverage (fun z => ‖mollifierError N z‖ ^ 2) c R := by
    apply circleAverage_mono
    · exact (hd.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · exact ((he.continuousOn.mono sphere_subset_closedBall).norm.pow 2).circleIntegrable'
    · intro z _
      exact log_norm_one_sub_sq_le _
  linarith

end Sidon
