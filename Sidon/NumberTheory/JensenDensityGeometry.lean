import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # The uniform geometric reserve in an integrated Jensen argument -/

noncomputable section

namespace Sidon

/-- A horizontal reserve of `δ` leaves a radial reserve of `δ/2` on a vertical window. -/
theorem jensen_disc_window {σ δ y : ℝ} {ρ : ℂ}
    (_hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hy : |y - ρ.im| ≤ δ) :
    ‖((2 : ℂ) + (y : ℂ) * Complex.I) - ρ‖ ≤ (2 - σ) - δ / 2 := by
  have hR : 0 ≤ (2 - σ) - δ / 2 := by linarith
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_one]
  norm_num
  change (2 - ρ.re) * (2 - ρ.re) + (y - ρ.im) * (y - ρ.im) ≤
    ((2 - σ) - δ / 2) ^ 2
  have hreal : 0 ≤ 2 - ρ.re := by linarith
  have hreal' : 2 - ρ.re ≤ (2 - σ) - δ := by linarith
  have him := sq_le_sq₀ (abs_nonneg (y - ρ.im)) hδ0 |>.mpr hy
  rw [sq_abs] at him
  have hsq := mul_self_le_mul_self hreal hreal'
  have hdR := mul_le_mul_of_nonneg_left hσ1 hδ0
  have hdδ := mul_le_mul_of_nonneg_left hδ1 hδ0
  nlinarith

/-- Jensen's logarithmic weight is uniformly positive on the vertical zero window. -/
theorem jensen_log_weight_lower {R d δ : ℝ} (hR0 : 1 ≤ R) (hR1 : R ≤ 3 / 2)
    (hd : 0 < d) (hδ : 0 ≤ δ) (hreserve : d ≤ R - δ / 2) :
    δ / 3 ≤ Real.log (R / d) := by
  have hR : 0 < R := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hR hd)
  rw [inv_div] at hlog
  have hdiv : d / R ≤ 1 - δ / (2 * R) := by
    apply (div_le_iff₀ hR).mpr
    field_simp
    nlinarith
  have hδdiv : δ / 3 ≤ δ / (2 * R) := by
    apply div_le_div_of_nonneg_left hδ (by positivity)
    linarith
  linarith

/-- The vertical line on which the balanced mollifier stays away from zero. -/
def jensenCenter (y : ℝ) : ℂ := 2 + (y : ℂ) * Complex.I

/-- The nonnegative logarithmic weight in Jensen's formula. -/
def jensenVerticalWeight (R : ℝ) (ρ : ℂ) (y : ℝ) : ℝ :=
  max 0 (Real.log R - Real.log ‖jensenCenter y - ρ‖)

theorem one_le_norm_jensenCenter_sub {ρ : ℂ} (hρ : ρ.re ≤ 1) (y : ℝ) :
    1 ≤ ‖jensenCenter y - ρ‖ := by
  have hh := Complex.re_le_norm (jensenCenter y - ρ)
  have hre : (jensenCenter y - ρ).re = 2 - ρ.re := by
    simp [jensenCenter]
  rw [hre] at hh
  linarith

theorem continuous_jensenVerticalWeight (R : ℝ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    Continuous (jensenVerticalWeight R ρ) := by
  have hc : Continuous (fun y : ℝ => ‖jensenCenter y - ρ‖) := by
    unfold jensenCenter
    fun_prop
  exact continuous_const.max (continuous_const.sub (hc.log (fun y =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hρ y)))))

theorem jensenVerticalWeight_lower {σ δ y : ℝ} {ρ : ℂ}
    (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hy : |y - ρ.im| ≤ δ) :
    δ / 3 ≤ jensenVerticalWeight (2 - σ) ρ y := by
  have hd : 0 < ‖jensenCenter y - ρ‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hβhi y)
  have hh := jensen_log_weight_lower (R := 2 - σ)
    (by linarith) (by linarith) hd hδ0
    (jensen_disc_window hσ0 hσ1 hδ0 hδ1 hβlo hβhi hy)
  rw [Real.log_div (by linarith) hd.ne'] at hh
  exact hh.trans (le_max_right _ _)

/-- Integrating in the center height gives every zero a uniform mass. -/
theorem jensenVerticalWeight_integral_lower {σ δ T : ℝ} {ρ : ℂ}
    (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hγlo : 4 ≤ ρ.im) (hγhi : ρ.im ≤ T) :
    2 * δ ^ 2 / 3 ≤ ∫ y in (3 : ℝ)..T + 1, jensenVerticalWeight (2 - σ) ρ y := by
  have hc := continuous_jensenVerticalWeight (2 - σ) hβhi
  have hab : ρ.im - δ ≤ ρ.im + δ := by linarith
  have hlocal : (∫ _ in ρ.im - δ..ρ.im + δ, δ / 3) ≤
      ∫ y in ρ.im - δ..ρ.im + δ, jensenVerticalWeight (2 - σ) ρ y := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (hc.intervalIntegrable _ _)
    intro y hy
    apply jensenVerticalWeight_lower hσ0 hσ1 hδ0 hδ1 hβlo hβhi
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hglobal := intervalIntegral.integral_mono_interval
    (μ := MeasureTheory.volume)
    (by linarith : (3 : ℝ) ≤ ρ.im - δ) hab
    (by linarith : ρ.im + δ ≤ T + 1)
    (f := jensenVerticalWeight (2 - σ) ρ)
    (MeasureTheory.ae_of_all _ (fun y => le_max_left 0 _)) (hc.intervalIntegrable _ _)
  calc
    2 * δ ^ 2 / 3 = ∫ _ in ρ.im - δ..ρ.im + δ, δ / 3 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := hlocal
    _ ≤ _ := hglobal

/-- Counting with repeated indices includes zero multiplicities without a separate argument. -/
theorem card_mul_jensen_mass_le_integral {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    {σ δ T : ℝ} (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : ∀ i ∈ S, σ + δ ≤ (ρ i).re)
    (hβhi : ∀ i ∈ S, (ρ i).re ≤ 1)
    (hγlo : ∀ i ∈ S, 4 ≤ (ρ i).im)
    (hγhi : ∀ i ∈ S, (ρ i).im ≤ T) :
    (S.card : ℝ) * (2 * δ ^ 2 / 3) ≤
      ∫ y in (3 : ℝ)..T + 1, ∑ i ∈ S, jensenVerticalWeight (2 - σ) (ρ i) y := by
  calc
    _ = ∑ i ∈ S, (2 * δ ^ 2 / 3) := by simp
    _ ≤ ∑ i ∈ S, ∫ y in (3 : ℝ)..T + 1,
        jensenVerticalWeight (2 - σ) (ρ i) y := by
      apply Finset.sum_le_sum
      intro i hi
      exact jensenVerticalWeight_integral_lower hσ0 hσ1 hδ0 hδ1
        (hβlo i hi) (hβhi i hi) (hγlo i hi) (hγhi i hi)
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (continuous_jensenVerticalWeight (2 - σ) (hβhi i hi)).intervalIntegrable _ _

end Sidon
