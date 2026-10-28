module

public import Sidon.NumberTheory.BSplinePrimitive

@[expose] public section

/-! Repeated primitives and exact smoothing of exponential zero atoms. -/

noncomputable section

open MeasureTheory

namespace Sidon

def logarithmicPrimitive (f : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f
  | n + 1 => fun t => ∫ u in (0 : ℝ)..t, logarithmicPrimitive f n u

theorem continuous_logarithmicPrimitive {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) :
    Continuous (logarithmicPrimitive f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      exact intervalIntegral.continuous_primitive (fun a b => ih.intervalIntegrable a b) 0

theorem fwdDiff_logarithmicPrimitive_succ {f : ℝ → ℂ} (hf : Continuous f)
    (n : ℕ) (h t : ℝ) :
    fwdDiff h (logarithmicPrimitive f (n + 1)) t =
      ∫ u in (0 : ℝ)..h, logarithmicPrimitive f n (t + u) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (logarithmicPrimitive f n) volume a b :=
    fun a b => (continuous_logarithmicPrimitive hf n).intervalIntegrable a b
  rw [fwdDiff, logarithmicPrimitive, intervalIntegral.integral_interval_sub_left
    (hi 0 (t + h)) (hi 0 t)]
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero]

def spectralSmoothing (n : ℕ) (h : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (fwdDiff h)^[n + 2] (logarithmicPrimitive f n) t

theorem spectralSmoothing_recursion {f : ℝ → ℂ} (hf : Continuous f)
    (n : ℕ) (h t : ℝ) :
    spectralSmoothing (n + 1) h f t =
      ∫ u in (0 : ℝ)..h, spectralSmoothing n h f (t + u) := by
  change (fwdDiff h)^[n + 2 + 1] (logarithmicPrimitive f (n + 1)) t = _
  rw [Function.iterate_succ_apply]
  have hh : fwdDiff h (logarithmicPrimitive f (n + 1)) =
      fun x => ∫ u in (0 : ℝ)..h, logarithmicPrimitive f n (x + u) :=
    funext (fwdDiff_logarithmicPrimitive_succ hf n h)
  rw [hh, fwdDiff_iter_intervalIntegral
    (fun a b => (continuous_logarithmicPrimitive hf n).intervalIntegrable a b)]
  rfl

theorem logarithmicPrimitive_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℕ) (t : ℝ) :
    logarithmicPrimitive (f + g) n t =
      logarithmicPrimitive f n t + logarithmicPrimitive g n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      change (∫ u in (0 : ℝ)..t, logarithmicPrimitive (f + g) n u) = _
      simp_rw [ih]
      exact intervalIntegral.integral_add
        ((continuous_logarithmicPrimitive hf n).intervalIntegrable 0 t)
        ((continuous_logarithmicPrimitive hg n).intervalIntegrable 0 t)

theorem logarithmicPrimitive_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    logarithmicPrimitive (fun u => c * f u) n t = c * logarithmicPrimitive f n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      change (∫ u in (0 : ℝ)..t, logarithmicPrimitive (fun v => c * f v) n u) = _
      simp_rw [ih]
      exact intervalIntegral.integral_const_mul _ _

theorem spectralSmoothing_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℕ) (h t : ℝ) :
    spectralSmoothing n h (f + g) t =
      spectralSmoothing n h f t + spectralSmoothing n h g t := by
  have hp : logarithmicPrimitive (f + g) n =
      logarithmicPrimitive f n + logarithmicPrimitive g n :=
    funext (logarithmicPrimitive_add hf hg n)
  unfold spectralSmoothing
  rw [hp, fwdDiff_iter_add]
  rfl

theorem spectralSmoothing_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℕ) (h t : ℝ) :
    spectralSmoothing n h (fun u => c * f u) t = c * spectralSmoothing n h f t := by
  have hp : logarithmicPrimitive (fun u => c * f u) n = c • logarithmicPrimitive f n :=
    funext (logarithmicPrimitive_const_mul c f n)
  unfold spectralSmoothing
  rw [hp, fwdDiff_iter_const_smul]
  rfl

theorem spectralSmoothing_affine (a b : ℂ) (n : ℕ) (h t : ℝ) :
    spectralSmoothing n h (fun u => a * u + b) t = 0 := by
  induction n generalizing t with
  | zero =>
      change ((a * ((t + h + h : ℝ) : ℂ) + b) - (a * ((t + h : ℝ) : ℂ) + b)) -
        ((a * ((t + h : ℝ) : ℂ) + b) - (a * t + b)) = 0
      push_cast
      ring
  | succ n ih =>
      rw [spectralSmoothing_recursion (by fun_prop : Continuous (fun u : ℝ => a * u + b))]
      simp_rw [ih]
      simp

theorem logarithmicPrimitive_congr_nonneg {f g : ℝ → ℂ}
    (hfg : ∀ t, 0 ≤ t → f t = g t) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    logarithmicPrimitive f n t = logarithmicPrimitive g n t := by
  induction n generalizing t with
  | zero => exact hfg t ht
  | succ n ih =>
      change (∫ u in (0 : ℝ)..t, logarithmicPrimitive f n u) =
        ∫ u in (0 : ℝ)..t, logarithmicPrimitive g n u
      apply intervalIntegral.integral_congr_Ioo_of_le ht
      intro u hu
      exact ih hu.1.le

theorem spectralSmoothing_congr_nonneg {f g : ℝ → ℂ}
    (hfg : ∀ t, 0 ≤ t → f t = g t) (n : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    spectralSmoothing n h f t = spectralSmoothing n h g t := by
  unfold spectralSmoothing
  simp only [fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply logarithmicPrimitive_congr_nonneg hfg
  exact add_nonneg ht (nsmul_nonneg hh k)

def exponentialZeroAtom (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (z * t) - 1) / z ^ 2

theorem continuous_exponentialZeroAtom (z : ℂ) : Continuous (exponentialZeroAtom z) := by
  unfold exponentialZeroAtom
  fun_prop

theorem integral_cexp_translate {z : ℂ} (hz : z ≠ 0) (h t : ℝ) :
    (∫ u in (0 : ℝ)..h, Complex.exp (z * ((t + u : ℝ) : ℂ))) =
      Complex.exp (z * t) * ((Complex.exp (z * h) - 1) / z) := by
  simp_rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hz]
  simp

theorem spectralSmoothing_exponentialZeroAtom {z : ℂ} (hz : z ≠ 0)
    (n : ℕ) (h t : ℝ) :
    spectralSmoothing n h (exponentialZeroAtom z) t =
      Complex.exp (z * t) * ((Complex.exp (z * h) - 1) / z) ^ (n + 2) := by
  induction n generalizing t with
  | zero =>
      change ((Complex.exp (z * ((t + h + h : ℝ) : ℂ)) - 1) / z ^ 2 -
          (Complex.exp (z * ((t + h : ℝ) : ℂ)) - 1) / z ^ 2) -
        ((Complex.exp (z * ((t + h : ℝ) : ℂ)) - 1) / z ^ 2 -
          (Complex.exp (z * t) - 1) / z ^ 2) = _
      simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
      rw [div_pow]
      field_simp
      ring
  | succ n ih =>
      rw [spectralSmoothing_recursion (continuous_exponentialZeroAtom z)]
      simp_rw [ih]
      rw [intervalIntegral.integral_mul_const, integral_cexp_translate hz]
      ring

end Sidon
