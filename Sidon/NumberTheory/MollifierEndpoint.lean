module

public import Sidon.NumberTheory.LogarithmicMeanSquare
public import Sidon.NumberTheory.HarmonicGaps

@[expose] public section

/-! # Critical-line finite mollifier mean squares -/

noncomputable section

namespace Sidon

theorem sum_Icc_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt N := by
  have hh := Finset.sum_Ico_add' (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) 0 N 1
  simp only [Nat.Ico_zero_eq_range, zero_add, Finset.Ico_add_one_right_eq_Icc,
    Nat.cast_add, Nat.cast_one] at hh
  rw [← hh]
  exact sum_range_inv_sqrt_succ_le N

theorem logarithmic_kernel_abs_le {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / (Real.sqrt m * Real.sqrt n * |Real.log n - Real.log m|) ≤
      1 / (Real.sqrt m * Real.sqrt n) + 1 / |n - m| := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hm h)), abs_of_pos (sub_pos.mpr h),
      ← Real.log_div hn.ne' hm.ne']
    exact logarithmic_kernel_le hm h
  · rw [abs_sub_comm (Real.log n), abs_sub_comm n,
      abs_of_pos (sub_pos.mpr (Real.log_lt_log hn h)), abs_of_pos (sub_pos.mpr h),
      ← Real.log_div hm.ne' hn.ne', mul_comm (Real.sqrt m) (Real.sqrt n)]
    exact logarithmic_kernel_le hn h

/-- The finite critical-line mean square needed for Ingham's mollifier. -/
theorem integral_logarithmicPolynomial_norm_sq_le_harmonic {N : ℕ} {a : ℕ → ℂ} {T : ℝ}
    (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ 1 / Real.sqrt (n : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial (Finset.Icc 1 N) a t‖ ^ 2) ≤
      T * (harmonic N : ℝ) + 8 * N + 4 * N * (harmonic N : ℝ) := by
  let S := Finset.Icc 1 N
  have hpos (n : ℕ) (hn : n ∈ S) : (0 : ℝ) < n := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hdiag : (∑ n ∈ S, ‖a n‖ ^ 2) ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hr := Real.sq_sqrt (hpos n hn).le
    calc
      ‖a n‖ ^ 2 ≤ (1 / Real.sqrt (n : ℝ)) ^ 2 := by gcongr; exact ha n hn
      _ = (n : ℝ)⁻¹ := by rw [div_pow, one_pow, hr, one_div]
  have hpair (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) :
      (if m = n then 0 else 2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m|) ≤
        2 / (Real.sqrt (m : ℝ) * Real.sqrt n) +
        2 * (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
    by_cases heq : m = n
    · subst n
      simp
      positivity
    · simp only [heq, ite_false]
      have hne : (m : ℝ) ≠ n := by exact_mod_cast heq
      have hh := logarithmic_kernel_abs_le (hpos m hm) (hpos n hn) hne
      calc
        _ ≤ 2 * (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ)) /
            |Real.log (n : ℝ) - Real.log m| := by gcongr <;> exact ha _ (by assumption)
        _ = 2 * (1 / (Real.sqrt (m : ℝ) * Real.sqrt n *
            |Real.log (n : ℝ) - Real.log m|)) := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
          simpa only [mul_add, mul_one_div, abs_sub_comm] using this
  have hproduct : (∑ m ∈ S, ∑ n ∈ S,
      1 / (Real.sqrt (m : ℝ) * Real.sqrt n)) ≤ 4 * N := by
    have heq : (∑ m ∈ S, ∑ n ∈ S, 1 / (Real.sqrt (m : ℝ) * Real.sqrt n)) =
        (∑ n ∈ S, 1 / Real.sqrt (n : ℝ)) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      simp only [one_div, mul_inv]
    rw [heq]
    have hh := sum_Icc_inv_sqrt_le N
    have hn0 : 0 ≤ ∑ n ∈ S, 1 / Real.sqrt (n : ℝ) := by positivity
    have hsquare := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith
  have hgap : (∑ m ∈ S, ∑ n ∈ S, if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) ≤
      2 * N * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ S, 2 * (harmonic N : ℝ) :=
        Finset.sum_le_sum fun m hm => sum_reciprocal_gap_le hm
      _ = _ := by simp [S]; ring
  apply (integral_logarithmicPolynomial_norm_sq_le S a T
    (fun n hn => (Finset.mem_Icc.mp hn).1)).trans
  have hdouble := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpair m hm n hn
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, one_mul, ← Finset.mul_sum] at hdouble
  have hdiag' := mul_le_mul_of_nonneg_left hdiag hT
  have hproduct' := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 2)
  have hgap' := mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2)
  simp only [div_eq_mul_inv, one_mul] at hproduct' hgap' ⊢
  linarith

/-- A uniform endpoint bound for arbitrary coefficients dominated by `n⁻¹ᐟ²`. -/
theorem integral_logarithmicPolynomial_norm_sq_le_log {N : ℕ} {a : ℕ → ℂ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ 1 / Real.sqrt (n : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial (Finset.Icc 1 N) a t‖ ^ 2) ≤
      12 * (T + N) * (1 + Real.log N) := by
  have hHone : (1 : ℝ) ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    have hh := Finset.single_le_sum (f := fun n : ℕ => (n : ℝ)⁻¹)
      (fun n (_ : n ∈ Finset.Icc 1 N) => by positivity)
      (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
    simpa only [Nat.cast_one, inv_one] using hh
  have hlog := harmonic_le_one_add_log N
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc
    _ ≤ T * (harmonic N : ℝ) + 8 * N + 4 * N * (harmonic N : ℝ) :=
      integral_logarithmicPolynomial_norm_sq_le_harmonic hT ha
    _ ≤ (T + 12 * N) * (harmonic N : ℝ) := by nlinarith
    _ ≤ (T + 12 * N) * (1 + Real.log N) := by gcongr
    _ ≤ _ := by nlinarith

/-- The literal finite Möbius mollifier at real part `1/2`. -/
def criticalMollifier (N : ℕ) (t : ℝ) : ℂ :=
  logarithmicPolynomial (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.moebius n : ℂ) / (Real.sqrt n : ℂ)) t

theorem norm_criticalMollifier_coefficient_le (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) / (Real.sqrt n : ℂ)‖ ≤
      1 / Real.sqrt n := by
  rw [norm_div, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- Ingham's critical-line finite-polynomial estimate, with an absolute constant. -/
theorem integral_criticalMollifier_norm_sq_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖criticalMollifier N t‖ ^ 2) ≤
      12 * (T + N) * (1 + Real.log N) :=
  integral_logarithmicPolynomial_norm_sq_le_log hN hT
    (fun n _ => norm_criticalMollifier_coefficient_le n)

end Sidon
