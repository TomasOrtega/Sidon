import Sidon.Equidistribution.Bohr
import Sidon.Equidistribution.ProgressionL1

/-! # A continuous probability bump on the unit circle -/

noncomputable section

open MeasureTheory

namespace Sidon

def circleRamp (η : ℝ) : C(AddCircle (1 : ℝ), ℝ) where
  toFun := clippedNormRamp (η / 2) (η / 4)
  continuous_toFun := by unfold clippedNormRamp; fun_prop

def circleBump (η : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  (∫ x : AddCircle (1 : ℝ), circleRamp η x ∂circleHaar)⁻¹ • circleRamp η

private theorem circle_integrable {f : AddCircle (1 : ℝ) → ℝ} (hf : Continuous f) :
    Integrable f circleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_circleRamp_lower {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    η / 2 ≤ ∫ x : AddCircle (1 : ℝ), circleRamp η x ∂circleHaar := by
  let A := Metric.closedBall (0 : AddCircle (1 : ℝ)) (η / 4)
  have hA : MeasurableSet A := measurableSet_closedBall
  have hvol : circleHaar A = ENNReal.ofReal (η / 2) := by
    rw [circleHaar_eq_volume, AddCircle.volume_closedBall]
    rw [min_eq_right (by linarith : 2 * (η / 4) ≤ (1 : ℝ))]
    congr 1
    ring
  have hcomp : (∫ x : AddCircle (1 : ℝ), A.indicator (fun _ => (1 : ℝ)) x ∂circleHaar) ≤
      ∫ x : AddCircle (1 : ℝ), circleRamp η x ∂circleHaar := by
    apply integral_mono ((integrable_const (1 : ℝ)).indicator hA)
      (circle_integrable (circleRamp η).continuous)
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hx' : ‖x‖ ≤ η / 2 - η / 4 := by
        have := Metric.mem_closedBall.mp hx
        rw [dist_zero_right] at this
        linarith
      change (1 : ℝ) ≤ clippedNormRamp (η / 2) (η / 4) x
      rw [clippedNormRamp_eq_one (by positivity) hx']
    · rw [Set.indicator_of_notMem hx]
      exact clippedNormRamp_nonneg _ _ _
  rw [integral_indicator_const (1 : ℝ) hA, measureReal_def, hvol,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_one] at hcomp
  exact hcomp

theorem circleBump_nonneg {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 2)
    (x : AddCircle (1 : ℝ)) : 0 ≤ circleBump η x := by
  have hc : 0 < ∫ y : AddCircle (1 : ℝ), circleRamp η y ∂circleHaar :=
    lt_of_lt_of_le (by positivity) (integral_circleRamp_lower hη hη₁)
  exact mul_nonneg (inv_nonneg.mpr hc.le) (clippedNormRamp_nonneg _ _ _)

theorem integral_circleBump {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    (∫ x : AddCircle (1 : ℝ), circleBump η x ∂circleHaar) = 1 := by
  have hc : 0 < ∫ y : AddCircle (1 : ℝ), circleRamp η y ∂circleHaar :=
    lt_of_lt_of_le (by positivity) (integral_circleRamp_lower hη hη₁)
  change (∫ x : AddCircle (1 : ℝ),
    (∫ y : AddCircle (1 : ℝ), circleRamp η y ∂circleHaar)⁻¹ • circleRamp η x ∂circleHaar) = 1
  rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hc)]

theorem circleBump_eq_zero {η : ℝ} (hη : 0 < η) {x : AddCircle (1 : ℝ)}
    (hx : η / 2 < ‖x‖) : circleBump η x = 0 := by
  change _ * clippedNormRamp (η / 2) (η / 4) x = 0
  rw [clippedNormRamp_eq_zero (by positivity) hx.le, mul_zero]

theorem integral_sq_circleBump_le {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    (∫ x : AddCircle (1 : ℝ), ‖circleBump η x‖ ^ 2 ∂circleHaar) ≤ 2 / η := by
  let c : ℝ := ∫ y : AddCircle (1 : ℝ), circleRamp η y ∂circleHaar
  have hlower : η / 2 ≤ c := integral_circleRamp_lower hη hη₁
  have hc : 0 < c := lt_of_lt_of_le (by positivity) hlower
  have hbound (x : AddCircle (1 : ℝ)) : circleBump η x ≤ c⁻¹ := by
    change c⁻¹ * clippedNormRamp (η / 2) (η / 4) x ≤ c⁻¹
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (clippedNormRamp_le_one (η / 2) (η / 4) x)
        (inv_nonneg.mpr hc.le)
  have hpoint (x : AddCircle (1 : ℝ)) : ‖circleBump η x‖ ^ 2 ≤ c⁻¹ * circleBump η x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (circleBump_nonneg hη hη₁ x)]
    nlinarith [mul_nonneg (circleBump_nonneg hη hη₁ x) (sub_nonneg.mpr (hbound x))]
  calc
    (∫ x : AddCircle (1 : ℝ), ‖circleBump η x‖ ^ 2 ∂circleHaar) ≤
        ∫ x : AddCircle (1 : ℝ), c⁻¹ • circleBump η x ∂circleHaar := by
      exact integral_mono (circle_integrable (by fun_prop))
        (circle_integrable (by fun_prop)) hpoint
    _ = c⁻¹ := by rw [integral_smul, integral_circleBump hη hη₁, smul_eq_mul, mul_one]
    _ ≤ (η / 2)⁻¹ := (inv_le_inv₀ hc (by positivity)).mpr hlower
    _ = 2 / η := by ring

theorem exists_circleBump {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    ∃ v : C(AddCircle (1 : ℝ), ℝ),
      (∀ x, 0 ≤ v x) ∧ (∫ x : AddCircle (1 : ℝ), v x ∂circleHaar) = 1 ∧
      (∀ x, η / 2 < ‖x‖ → v x = 0) ∧
      (∫ x : AddCircle (1 : ℝ), ‖v x‖ ^ 2 ∂circleHaar) ≤ 10 / η := by
  refine ⟨circleBump η, circleBump_nonneg hη hη₁, integral_circleBump hη hη₁,
    fun _ hx => circleBump_eq_zero hη hx, ?_⟩
  exact (integral_sq_circleBump_le hη hη₁).trans
    (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 10) hη.le)

end Sidon
