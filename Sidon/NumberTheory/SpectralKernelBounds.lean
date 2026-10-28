module

public import Sidon.NumberTheory.LogSmoothing

@[expose] public section

/-! Low-frequency and high-frequency bounds for the exact exponential kernel. -/

noncomputable section

open MeasureTheory

namespace Sidon

theorem norm_exp_sub_one_div_le {z : ℂ} (hz : z ≠ 0) (hβ : 0 ≤ z.re)
    {h : ℝ} (hh : 0 ≤ h) :
    ‖(Complex.exp (z * h) - 1) / z‖ ≤ Real.exp (z.re * h) * h := by
  have he : (Complex.exp (z * h) - 1) / z =
      ∫ u in (0 : ℝ)..h, Complex.exp (z * u) := by
    simpa using (integral_cexp_translate hz h 0).symm
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := h) (C := Real.exp (z.re * h))
    (f := fun u : ℝ => Complex.exp (z * u)) (fun u hu => by
      rw [Set.uIoc_of_le hh] at hu
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hβ))
  simpa only [sub_zero, abs_of_nonneg hh] using hb

theorem norm_exp_sub_one_div_le_two {z : ℂ} (hβ : 0 ≤ z.re)
    {h : ℝ} (hh : 0 ≤ h) :
    ‖(Complex.exp (z * h) - 1) / z‖ ≤ 2 * Real.exp (z.re * h) / ‖z‖ := by
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg z)
  have hE : 1 ≤ Real.exp (z.re * h) := Real.one_le_exp_iff.mpr (mul_nonneg hβ hh)
  calc
    ‖Complex.exp (z * h) - 1‖ ≤ ‖Complex.exp (z * h)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.exp (z.re * h) + 1 := by simp [Complex.norm_exp]
    _ ≤ _ := by linarith

theorem spectralSmoothing_exponentialZeroAtom_norm_le {z : ℂ} (hz : z ≠ 0)
    (hβ : 0 ≤ z.re) (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    ‖spectralSmoothing n h (exponentialZeroAtom z) t‖ ≤
      Real.exp (z.re * (t + ((n + 2 : ℕ) : ℝ) * h)) * h ^ (n + 2) := by
  rw [spectralSmoothing_exponentialZeroAtom hz, norm_mul, norm_pow, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp (z.re * t) * (Real.exp (z.re * h) * h) ^ (n + 2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_exp_sub_one_div_le hz hβ hh) _) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem spectralSmoothing_exponentialZeroAtom_norm_le_high {z : ℂ} (hz : z ≠ 0)
    (hβ : 0 ≤ z.re) (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    ‖spectralSmoothing n h (exponentialZeroAtom z) t‖ ≤
      Real.exp (z.re * (t + ((n + 2 : ℕ) : ℝ) * h)) *
        (2 : ℝ) ^ (n + 2) / ‖z‖ ^ (n + 2) := by
  rw [spectralSmoothing_exponentialZeroAtom hz, norm_mul, norm_pow, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp (z.re * t) * (2 * Real.exp (z.re * h) / ‖z‖) ^ (n + 2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_exp_sub_one_div_le_two hβ hh) _) (Real.exp_pos _).le
    _ = _ := by
      rw [div_pow, mul_pow, ← Real.exp_nat_mul]
      have hE : Real.exp (z.re * t) * Real.exp (((n + 2 : ℕ) : ℝ) * (z.re * h)) =
          Real.exp (z.re * (t + ((n + 2 : ℕ) : ℝ) * h)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (z.re * t) * Real.exp (((n + 2 : ℕ) : ℝ) * (z.re * h))) *
            2 ^ (n + 2) / ‖z‖ ^ (n + 2) := by ring
        _ = _ := by rw [hE]

theorem exponential_mainTerm_lower_bound (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    Real.exp t * h ^ r ≤ Real.exp t * (Real.exp h - 1) ^ r := by
  have hE : h ≤ Real.exp h - 1 := by linarith [Real.add_one_le_exp h]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hE r) (Real.exp_pos t).le

theorem exponential_mainTerm_lower_bound_at_log (r : ℕ) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (hrh : (r : ℝ) * h ≤ Real.log 2) :
    x / 2 * h ^ r ≤
      Real.exp (Real.log x - (r : ℝ) * h) * (Real.exp h - 1) ^ r := by
  have hE : Real.exp ((r : ℝ) * h) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hrh
  have hxE : x / 2 ≤ Real.exp (Real.log x - (r : ℝ) * h) := by
    rw [Real.exp_sub, Real.exp_log hx]
    exact div_le_div_of_nonneg_left hx.le (Real.exp_pos _) hE
  exact (mul_le_mul_of_nonneg_right hxE (pow_nonneg hh r)).trans
    (exponential_mainTerm_lower_bound r hh _)

end Sidon
