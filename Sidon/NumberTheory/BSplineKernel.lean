module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! # Positive compactly supported kernels from finite differences -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

def heaviside (u : ℝ) : ℝ := if 0 ≤ u then 1 else 0

theorem measurable_heaviside : Measurable heaviside :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem heaviside_nonneg (u : ℝ) : 0 ≤ heaviside u := by
  unfold heaviside
  split_ifs <;> norm_num

theorem heaviside_le_one (u : ℝ) : heaviside u ≤ 1 := by
  unfold heaviside
  split_ifs <;> norm_num

theorem intervalIntegrable_heaviside (a b : ℝ) :
    IntervalIntegrable heaviside volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    measurable_heaviside.aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖heaviside u‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (heaviside_nonneg u)]
    exact heaviside_le_one u

def heavisidePrimitive : ℕ → ℝ → ℝ
  | 0 => heaviside
  | n + 1 => fun u => ∫ v in (0 : ℝ)..u, heavisidePrimitive n v

theorem intervalIntegrable_heavisidePrimitive (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (heavisidePrimitive n) volume a b := by
  induction n generalizing a b with
  | zero => exact intervalIntegrable_heaviside a b
  | succ n ih =>
      exact (intervalIntegral.continuous_primitive ih 0).intervalIntegrable a b

theorem continuous_heavisidePrimitive_succ (n : ℕ) :
    Continuous (heavisidePrimitive (n + 1)) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_heavisidePrimitive n) 0

theorem heavisidePrimitive_one (u : ℝ) : heavisidePrimitive 1 u = max u 0 := by
  change (∫ v in (0 : ℝ)..u, heaviside v) = max u 0
  by_cases hu : 0 ≤ u
  · have he : (∫ v in (0 : ℝ)..u, heaviside v) = ∫ _v in (0 : ℝ)..u, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hu
      intro v hv
      simp [heaviside, hv.1.le]
    rw [he]
    simp [intervalIntegral.integral_const, max_eq_left hu]
  · have hu' : u ≤ 0 := (lt_of_not_ge hu).le
    have he : (∫ v in u..(0 : ℝ), heaviside v) = ∫ _v in u..(0 : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hu'
      intro v hv
      simp [heaviside, not_le.mpr hv.2]
    rw [intervalIntegral.integral_symm, he]
    simp [max_eq_right hu']

theorem heavisidePrimitive_succ_eq_zero_of_nonpos (n : ℕ) {u : ℝ} (hu : u ≤ 0) :
    heavisidePrimitive (n + 1) u = 0 := by
  induction n generalizing u with
  | zero => rw [zero_add, heavisidePrimitive_one, max_eq_right hu]
  | succ n ih =>
      change (∫ v in (0 : ℝ)..u, heavisidePrimitive (n + 1) v) = 0
      rw [intervalIntegral.integral_symm]
      have he : (∫ v in u..(0 : ℝ), heavisidePrimitive (n + 1) v) =
          ∫ _v in u..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hu] at hv
        exact ih hv.2
      rw [he]
      simp

theorem integral_heavisidePrimitive_translate (n : ℕ) (a b c : ℝ) :
    (∫ v in a..b, heavisidePrimitive n (v + c)) =
      heavisidePrimitive (n + 1) (b + c) - heavisidePrimitive (n + 1) (a + c) := by
  rw [intervalIntegral.integral_comp_add_right]
  exact (intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_heavisidePrimitive n 0 (b + c))
    (intervalIntegrable_heavisidePrimitive n 0 (a + c))).symm

theorem intervalIntegrable_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (u a b : ℝ) :
    IntervalIntegrable (fun v => f (u + v)) volume a b := by
  have hh : IntervalIntegrable (fun v => f (v + u)) volume a b :=
    by simpa only [add_sub_cancel_right] using (hf (a + u) (b + u)).comp_add_right u
  simpa only [add_comm] using hh

theorem fwdDiff_heavisidePrimitive_succ (n : ℕ) (h u : ℝ) :
    fwdDiff h (heavisidePrimitive (n + 1)) u =
      ∫ v in (0 : ℝ)..h, heavisidePrimitive n (u + v) := by
  rw [fwdDiff, heavisidePrimitive, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_heavisidePrimitive n 0 (u + h))
    (intervalIntegrable_heavisidePrimitive n 0 u)]
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero]

theorem intervalIntegrable_fwdDiff_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (h : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable ((fwdDiff h)^[n] f) volume a b := by
  induction n generalizing a b with
  | zero => exact hf a b
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hh : IntervalIntegrable (fun x => ((fwdDiff h)^[n] f) (x + h)) volume a b := by
        simpa only [add_sub_cancel_right] using (ih (a + h) (b + h)).comp_add_right h
      exact hh.sub (ih a b)

theorem fwdDiff_iter_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (h : ℝ) (n : ℕ) (u : ℝ) :
    (fwdDiff h)^[n] (fun x => ∫ v in (0 : ℝ)..h, f (x + v)) u =
      ∫ v in (0 : ℝ)..h, ((fwdDiff h)^[n] f) (u + v) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((fwdDiff h)^[n] (fun x => ∫ v in (0 : ℝ)..h, f (x + v)) (u + h) -
        (fwdDiff h)^[n] (fun x => ∫ v in (0 : ℝ)..h, f (x + v)) u) = _
      rw [ih, ih, ← intervalIntegral.integral_sub
        (intervalIntegrable_translate (intervalIntegrable_fwdDiff_iter hf h n) (u + h) 0 h)
        (intervalIntegrable_translate (intervalIntegrable_fwdDiff_iter hf h n) u 0 h)]
      apply intervalIntegral.integral_congr
      intro v _
      rw [Function.iterate_succ_apply']
      simp only [fwdDiff, add_comm, add_left_comm]

def primeDetectorKernel (r : ℕ) (h u : ℝ) : ℝ :=
  (fwdDiff h)^[r] (heavisidePrimitive (r - 1)) u

theorem primeDetectorKernel_eq_sum (r : ℕ) (h u : ℝ) :
    primeDetectorKernel r h u = ∑ j ∈ Finset.range (r + 1),
      ((-1 : ℝ) ^ (r - j) * (r.choose j : ℝ)) *
        heavisidePrimitive (r - 1) (u + (j : ℝ) * h) := by
  simpa only [primeDetectorKernel, zsmul_eq_mul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using
    fwdDiff_iter_eq_sum_shift h (heavisidePrimitive (r - 1)) r u

@[simp] theorem primeDetectorKernel_succ (n : ℕ) (h u : ℝ) :
    primeDetectorKernel (n + 1) h u =
      (fwdDiff h)^[n + 1] (heavisidePrimitive n) u := by
  simp only [primeDetectorKernel, Nat.add_sub_cancel]

theorem primeDetectorKernel_recursion (n : ℕ) (h u : ℝ) :
    primeDetectorKernel (n + 2) h u =
      ∫ v in (0 : ℝ)..h, primeDetectorKernel (n + 1) h (u + v) := by
  rw [show n + 2 = (n + 1) + 1 by omega, primeDetectorKernel_succ,
    Function.iterate_succ_apply]
  have hh : fwdDiff h (heavisidePrimitive (n + 1)) =
      fun x => ∫ v in (0 : ℝ)..h, heavisidePrimitive n (x + v) :=
    funext (fwdDiff_heavisidePrimitive_succ n h)
  rw [hh, fwdDiff_iter_intervalIntegral (intervalIntegrable_heavisidePrimitive n)]
  simp only [primeDetectorKernel_succ]

theorem intervalIntegrable_primeDetectorKernel (r : ℕ) (h a b : ℝ) :
    IntervalIntegrable (primeDetectorKernel r h) volume a b :=
  intervalIntegrable_fwdDiff_iter (intervalIntegrable_heavisidePrimitive (r - 1)) h r a b

@[simp] theorem primeDetectorKernel_one (h u : ℝ) :
    primeDetectorKernel 1 h u = heaviside (u + h) - heaviside u := rfl

theorem primeDetectorKernel_one_bounds {h : ℝ} (hh : 0 ≤ h) (u : ℝ) :
    0 ≤ primeDetectorKernel 1 h u ∧ primeDetectorKernel 1 h u ≤ 1 := by
  by_cases hu : 0 ≤ u
  · have huh : 0 ≤ u + h := add_nonneg hu hh
    simp only [primeDetectorKernel_one, heaviside, ite_eq_left hu,
      ite_eq_left huh, sub_self, le_refl, zero_le_one, and_self]
  · rw [primeDetectorKernel_one, show heaviside u = 0 by simp [heaviside, hu], sub_zero]
    exact ⟨heaviside_nonneg _, heaviside_le_one _⟩

theorem primeDetectorKernel_bounds_succ (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (u : ℝ) :
    0 ≤ primeDetectorKernel (n + 1) h u ∧ primeDetectorKernel (n + 1) h u ≤ h ^ n := by
  induction n generalizing u with
  | zero => simpa only [zero_add, pow_zero] using primeDetectorKernel_one_bounds hh u
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, primeDetectorKernel_recursion]
      refine ⟨intervalIntegral.integral_nonneg_of_forall hh (fun v => (ih (u + v)).1), ?_⟩
      calc
        _ ≤ ∫ _v in (0 : ℝ)..h, h ^ n := by
          apply intervalIntegral.integral_mono_on hh
            (intervalIntegrable_translate (intervalIntegrable_primeDetectorKernel (n + 1) h) u 0 h)
            intervalIntegrable_const
          exact fun v _ => (ih (u + v)).2
        _ = h ^ (n + 1) := by simp [intervalIntegral.integral_const, pow_succ, mul_comm]

theorem primeDetectorKernel_bounds {r : ℕ} (hr : 0 < r) {h : ℝ}
    (hh : 0 ≤ h) (u : ℝ) :
    0 ≤ primeDetectorKernel r h u ∧ primeDetectorKernel r h u ≤ h ^ (r - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    primeDetectorKernel_bounds_succ n hh u

theorem primeDetectorKernel_one_eq_zero {h u : ℝ} (hh : 0 ≤ h)
    (hu : u < -h ∨ 0 < u) : primeDetectorKernel 1 h u = 0 := by
  rcases hu with hu | hu
  · have hu0 : ¬ 0 ≤ u := by linarith
    have huh : ¬ 0 ≤ u + h := by linarith
    rw [primeDetectorKernel_one]
    simp [heaviside, hu0, huh]
  · rw [primeDetectorKernel_one]
    simp [heaviside, hu.le, add_nonneg hu.le hh]

theorem primeDetectorKernel_eq_zero_succ (n : ℕ) {h u : ℝ} (hh : 0 ≤ h)
    (hu : u < -((n + 1 : ℕ) : ℝ) * h ∨ 0 < u) :
    primeDetectorKernel (n + 1) h u = 0 := by
  induction n generalizing u with
  | zero =>
      have hu' : u < -h ∨ 0 < u := by simpa using hu
      exact primeDetectorKernel_one_eq_zero hh hu'
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, primeDetectorKernel_recursion]
      calc
        _ = ∫ _v in (0 : ℝ)..h, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [Set.uIcc_of_le hh] at hv
          apply ih
          rcases hu with hu | hu
          · left
            push_cast at hu ⊢
            nlinarith [hv.2]
          · right
            linarith [hv.1]
        _ = 0 := by simp

theorem primeDetectorKernel_eq_zero {r : ℕ} (hr : 0 < r) {h u : ℝ} (hh : 0 ≤ h)
    (hu : u < -(r : ℝ) * h ∨ 0 < u) : primeDetectorKernel r h u = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  exact primeDetectorKernel_eq_zero_succ n hh hu

theorem support_primeDetectorKernel_subset {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 ≤ h) :
    Function.support (primeDetectorKernel r h) ⊆ Set.Icc (-(r : ℝ) * h) 0 := by
  intro u hu
  by_contra hout
  have hhout : u < -(r : ℝ) * h ∨ 0 < u := by
    simpa only [Set.mem_Icc, not_and_or, not_le, or_comm] using hout
  exact hu (primeDetectorKernel_eq_zero hr hh hhout)

end Sidon
