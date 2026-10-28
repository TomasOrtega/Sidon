module

public import Sidon.NumberTheory.DirichletMeanSquare
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

/-! # Logarithmic frequencies and harmonic majorants -/

noncomputable section

namespace Sidon

/-- The logarithmic kernel used for the critical-line mollifier. -/
theorem logarithmic_kernel_le {m n : ℝ} (hm : 0 < m) (hmn : m < n) :
    1 / (Real.sqrt m * Real.sqrt n * Real.log (n / m)) ≤
      1 / (Real.sqrt m * Real.sqrt n) + 1 / (n - m) := by
  have hn : 0 < n := hm.trans hmn
  have hroot : 0 < Real.sqrt m * Real.sqrt n := mul_pos (Real.sqrt_pos.2 hm) (Real.sqrt_pos.2 hn)
  have hdiff : 0 < n - m := sub_pos.mpr hmn
  have hratio : 1 < n / m := (one_lt_div hm).mpr hmn
  have hlog : 0 < Real.log (n / m) := Real.log_pos hratio
  have hlow : n - m ≤ n * Real.log (n / m) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
    rw [inv_div] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hn.le
    field_simp at hh'
    nlinarith
  have hmroot : m ≤ Real.sqrt m * Real.sqrt n := by
    calc
      m = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmn.le) (Real.sqrt_nonneg m)
  calc
    _ ≤ n / ((Real.sqrt m * Real.sqrt n) * (n - m)) := by
      apply (div_le_div_iff₀ (mul_pos hroot hlog) (mul_pos hroot hdiff)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlow hroot.le]
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hroot hdiff)).mpr
      field_simp
      nlinarith

/-- A telescoping square-root bound, with no asymptotic constant. -/
theorem sum_range_inv_sqrt_succ_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / Real.sqrt ((n : ℝ) + 1)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hroot : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hstep : 1 / Real.sqrt ((N : ℝ) + 1) ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
      apply (div_le_iff₀ hroot).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        Real.sq_sqrt (show 0 ≤ (N : ℝ) + 1 by positivity),
        sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N)]
    push_cast
    linarith

/-- The finite polynomial used on the critical-line endpoint. -/
def logarithmicPolynomial (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  finiteFrequencySum s a (fun n => -Real.log n) t

@[fun_prop] theorem continuous_logarithmicPolynomial (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (logarithmicPolynomial s a) := continuous_finiteFrequencySum s a _

theorem integral_logarithmicPolynomial_norm_sq_le (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial s a t‖ ^ 2) ≤
      T * ∑ n ∈ s, ‖a n‖ ^ 2 +
        ∑ m ∈ s, ∑ n ∈ s, if m = n then 0 else
          2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m| := by
  have hω : Set.InjOn (fun n : ℕ => -Real.log n) (s : Set ℕ) := by
    intro m hm n hn h
    have he : Real.log (m : ℝ) = Real.log n := neg_injective h
    have hp := Real.log_injOn_pos
      (show (0 : ℝ) < m by exact_mod_cast hs m hm)
      (show (0 : ℝ) < n by exact_mod_cast hs n hn) he
    exact_mod_cast hp
  simpa only [logarithmicPolynomial, neg_sub_neg] using
    integral_finiteFrequencySum_norm_sq_le s a (fun n => -Real.log n) T hω

end Sidon
