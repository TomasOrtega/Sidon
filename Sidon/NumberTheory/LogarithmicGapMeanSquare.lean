module

public import Sidon.NumberTheory.LogarithmicMeanSquare
public import Sidon.NumberTheory.HarmonicGaps

@[expose] public section

/-! # A logarithmic off-diagonal bound uniform in the polynomial length -/

noncomputable section

namespace Sidon

def nearReciprocalGap (m n : ℕ) : ℝ :=
  if m = n then 0 else if n ≤ 2 * m ∧ m ≤ 2 * n then 1 / |(m : ℝ) - n| else 0

theorem nearReciprocalGap_nonneg (m n : ℕ) : 0 ≤ nearReciprocalGap m n := by
  unfold nearReciprocalGap
  split_ifs <;> positivity

theorem nearReciprocalGap_symm (m n : ℕ) :
    nearReciprocalGap m n = nearReciprocalGap n m := by
  unfold nearReciprocalGap
  by_cases h : m = n
  · subst n
    simp
  · simp only [h, Ne.symm h, ite_false]
    by_cases hnear : n ≤ 2 * m ∧ m ≤ 2 * n
    · simp only [hnear, and_comm.mp hnear, ite_true, abs_sub_comm]
    · simp only [hnear, show ¬(m ≤ 2 * n ∧ n ≤ 2 * m) by tauto, ite_false]

theorem sum_nearReciprocalGap_le (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ s, nearReciprocalGap m n) ≤ 4 * (1 + Real.log m) := by
  classical
  have hext : (∑ n ∈ s, nearReciprocalGap m n) ≤
      ∑ n ∈ Finset.Icc 1 (2 * m), if m = n then 0 else 1 / |(m : ℝ) - n| := by
    calc
      _ = ∑ n ∈ s.filter (fun n => n ≤ 2 * m ∧ m ≤ 2 * n),
          if m = n then 0 else 1 / |(m : ℝ) - n| := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        unfold nearReciprocalGap
        split_ifs <;> rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, hnm, _⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Icc.mpr ⟨hs n hn, hnm⟩
        · intro n _ _
          split_ifs <;> positivity
  have hg := sum_reciprocal_gap_le (m := m) (N := 2 * m)
    (Finset.mem_Icc.mpr ⟨hm, by omega⟩)
  have hh := harmonic_le_one_add_log (2 * m)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog : Real.log (2 * m : ℕ) = Real.log 2 + Real.log m := by
    push_cast
    rw [Real.log_mul (by norm_num) hm0.ne']
  rw [hlog] at hh
  exact hext.trans (hg.trans (by nlinarith))

theorem ordered_logarithmic_offDiagonal_le {m n a b : ℝ}
    (hm : 0 < m) (hmn : m < n) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / Real.log (n / m) ≤
      4 * a * b + if n ≤ 2 * m then 2 * (m * a ^ 2 + n * b ^ 2) / (n - m) else 0 := by
  have hn : 0 < n := hm.trans hmn
  have hlog : 0 < Real.log (n / m) := Real.log_pos ((one_lt_div hm).mpr hmn)
  have hlow : n - m ≤ n * Real.log (n / m) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
    rw [inv_div] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hn.le
    field_simp at hh'
    nlinarith
  by_cases hnear : n ≤ 2 * m
  · rw [if_pos hnear]
    have hnum : 2 * n * a * b ≤ 2 * (m * a ^ 2 + n * b ^ 2) := by
      have hsq := mul_nonneg hn.le (sq_nonneg (a - b))
      have hrem := mul_nonneg (show 0 ≤ 2 * m - n by linarith) (sq_nonneg a)
      nlinarith
    have hfrac : 2 * a * b / Real.log (n / m) ≤ 2 * n * a * b / (n - m) := by
      apply (div_le_div_iff₀ hlog (sub_pos.mpr hmn)).mpr
      have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * a * b by positivity)
      nlinarith
    calc
      _ ≤ 2 * n * a * b / (n - m) := hfrac
      _ ≤ 2 * (m * a ^ 2 + n * b ^ 2) / (n - m) :=
        div_le_div_of_nonneg_right hnum (sub_nonneg.mpr hmn.le)
      _ ≤ _ := by linarith [mul_nonneg ha hb]
  · rw [if_neg hnear, add_zero]
    have hratio : 2 ≤ n / m := (le_div_iff₀ hm).mpr (by linarith)
    have hhalf : (1 / 2 : ℝ) ≤ Real.log (n / m) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh.trans (Real.log_le_log (by norm_num) hratio)
    apply (div_le_iff₀ hlog).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4 * a * b by positivity)
    nlinarith

theorem logarithmic_offDiagonal_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if m = n then 0 else 2 * a * b / |Real.log (n : ℝ) - Real.log m|) ≤
      4 * a * b + 2 * ((m : ℝ) * a ^ 2 + n * b ^ 2) * nearReciprocalGap m n := by
  have ordered {m n : ℕ} (hm : 0 < m) (hmn : m < n) (a b : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b) :
      2 * a * b / |Real.log (n : ℝ) - Real.log m| ≤
        4 * a * b + 2 * ((m : ℝ) * a ^ 2 + n * b ^ 2) * nearReciprocalGap m n := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn0 : (m : ℝ) < n := by exact_mod_cast hmn
    have hn0 : (0 : ℝ) < n := hm0.trans hmn0
    have hlog : Real.log m < Real.log n := Real.log_lt_log hm0 hmn0
    rw [abs_of_pos (sub_pos.mpr hlog), ← Real.log_div hn0.ne' hm0.ne']
    have hh := ordered_logarithmic_offDiagonal_le hm0 hmn0 ha hb
    unfold nearReciprocalGap
    rw [if_neg (by omega : m ≠ n)]
    by_cases hnear : n ≤ 2 * m
    · rw [if_pos ⟨hnear, by omega⟩, abs_of_neg (sub_neg.mpr hmn0), neg_sub]
      have hnear0 : (n : ℝ) ≤ 2 * m := by exact_mod_cast hnear
      rw [if_pos hnear0] at hh
      simpa only [div_eq_mul_inv, one_div, mul_assoc, one_mul] using hh
    · rw [if_neg (by tauto), mul_zero, add_zero]
      have hnear0 : ¬(n : ℝ) ≤ 2 * m := by exact_mod_cast hnear
      simpa only [if_neg hnear0, add_zero] using hh
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg (by omega : m ≠ n)]
    exact ordered hm h a b ha hb
  · subst n
    simp only [nearReciprocalGap, ite_true, mul_zero, add_zero]
    positivity
  · rw [if_neg (by omega : m ≠ n)]
    have hh := ordered hn h b a hb ha
    rw [abs_sub_comm, nearReciprocalGap_symm n m] at hh
    convert hh using 1 <;> ring

/-- Only a logarithm of each coefficient's own index enters the off-diagonal cost. -/
theorem integral_logarithmicPolynomial_norm_sq_le_weighted (s : Finset ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial s a t‖ ^ 2) ≤
      T * ∑ n ∈ s, ‖a n‖ ^ 2 + 4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ s, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
  classical
  let q (n : ℕ) : ℝ := (n : ℝ) * ‖a n‖ ^ 2
  have hrow : (∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n) ≤
      4 * ∑ m ∈ s, q m * (1 + Real.log m) := by
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hh := mul_le_mul_of_nonneg_left (sum_nearReciprocalGap_le s hs (hs m hm))
      (show 0 ≤ q m by dsimp [q]; positivity)
    convert hh using 1 <;> ring
  have hcol : (∑ m ∈ s, ∑ n ∈ s, q n * nearReciprocalGap m n) =
      ∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    rw [nearReciprocalGap_symm n m]
  have hprod : (∑ m ∈ s, ∑ n ∈ s, 4 * ‖a m‖ * ‖a n‖) =
      4 * (∑ n ∈ s, ‖a n‖) ^ 2 := by
    calc
      _ = 4 * (∑ m ∈ s, ∑ n ∈ s, ‖a m‖ * ‖a n‖) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := by rw [← Finset.sum_mul_sum]; ring
  have hscale (f : ℕ → ℕ → ℝ) :
      (∑ m ∈ s, ∑ n ∈ s, 2 * f m n) = 2 * ∑ m ∈ s, ∑ n ∈ s, f m n := by
    simp only [Finset.mul_sum]
  have hoff : (∑ m ∈ s, ∑ n ∈ s,
      if m = n then 0 else 2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m|) ≤
      4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ s, q n * (1 + Real.log n) := by
    calc
      _ ≤ ∑ m ∈ s, ∑ n ∈ s,
          (4 * ‖a m‖ * ‖a n‖ + 2 * (q m + q n) * nearReciprocalGap m n) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact logarithmic_offDiagonal_le (hs m hm) (hs n hn) _ _ (norm_nonneg _) (norm_nonneg _)
      _ = 4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
          2 * (∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n) +
          2 * (∑ m ∈ s, ∑ n ∈ s, q n * nearReciprocalGap m n) := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib,
          show ∀ m n, 2 * q m * nearReciprocalGap m n =
            2 * (q m * nearReciprocalGap m n) by intros; ring,
          show ∀ m n, 2 * q n * nearReciprocalGap m n =
            2 * (q n * nearReciprocalGap m n) by intros; ring]
        rw [hprod, hscale, hscale]
        ring
      _ ≤ _ := by rw [hcol]; linarith
  have hh := integral_logarithmicPolynomial_norm_sq_le s a T hs
  exact hh.trans (by dsimp [q] at hoff; linarith)

end Sidon
