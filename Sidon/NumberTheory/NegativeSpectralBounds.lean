module

public import Sidon.NumberTheory.SpectralKernelBounds

@[expose] public section

/-! A reciprocal-square bound for the smoothed trivial-zero terms. -/

noncomputable section

open MeasureTheory

namespace Sidon

theorem norm_exp_sub_one_div_le_of_re_nonpos {z : ℂ} (hz : z ≠ 0) (hβ : z.re ≤ 0)
    {h : ℝ} (hh : 0 ≤ h) :
    ‖(Complex.exp (z * h) - 1) / z‖ ≤ h := by
  have he : (Complex.exp (z * h) - 1) / z =
      ∫ u in (0 : ℝ)..h, Complex.exp (z * u) := by
    simpa using (integral_cexp_translate hz h 0).symm
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := h) (C := (1 : ℝ))
    (f := fun u : ℝ => Complex.exp (z * u)) (fun u hu => by
      rw [Set.uIoc_of_le hh] at hu
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hβ hu.1.le))
  simpa only [sub_zero, abs_of_nonneg hh, one_mul] using hb

theorem norm_exp_sub_one_div_le_two_inv_of_re_nonpos {z : ℂ} (hβ : z.re ≤ 0)
    {h : ℝ} (hh : 0 ≤ h) :
    ‖(Complex.exp (z * h) - 1) / z‖ ≤ 2 / ‖z‖ := by
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg z)
  have he : ‖Complex.exp (z * h)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hβ hh)
  have hn := norm_sub_le (Complex.exp (z * h)) 1
  norm_num at hn
  linarith

theorem spectralSmoothing_exponentialZeroAtom_norm_le_nonpos {z : ℂ} (hz : z ≠ 0)
    (hβ : z.re ≤ 0) (n : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    ‖spectralSmoothing n h (exponentialZeroAtom z) t‖ ≤ 4 * h ^ n / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖Complex.exp (z * t)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hβ ht)
  rw [spectralSmoothing_exponentialZeroAtom hz, norm_mul, norm_pow]
  calc
    _ ≤ 1 * ‖(Complex.exp (z * h) - 1) / z‖ ^ (n + 2) :=
      mul_le_mul_of_nonneg_right he (pow_nonneg (norm_nonneg _) _)
    _ = ‖(Complex.exp (z * h) - 1) / z‖ ^ n *
        ‖(Complex.exp (z * h) - 1) / z‖ ^ 2 := by rw [one_mul, pow_add]
    _ ≤ h ^ n * (2 / ‖z‖) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
        (norm_exp_sub_one_div_le_of_re_nonpos hz hβ hh) n)
        (pow_le_pow_left₀ (norm_nonneg _)
          (norm_exp_sub_one_div_le_two_inv_of_re_nonpos hβ hh) 2)
        (sq_nonneg _) (pow_nonneg hh n)
    _ = _ := by ring

end Sidon
