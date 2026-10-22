import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Reciprocal gaps between distinct positive integers -/

noncomputable section

namespace Sidon

theorem sum_reciprocal_gap_le {N m : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N, if m = n then 0 else 1 / |(m : ℝ) - n|) ≤
      2 * (harmonic N : ℝ) := by
  classical
  let S := Finset.Icc 1 N
  have hlo : (∑ n ∈ S.filter (fun n => n < m), ((m - n : ℕ) : ℝ)⁻¹) ≤
      ∑ d ∈ S, (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => m - n)
    · intro n hn k hk heq
      have hn' := (Finset.mem_filter.mp hn).2
      have hk' := (Finset.mem_filter.mp hk).2
      change m - n = m - k at heq
      omega
    · intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hn, hnm⟩ := Finset.mem_filter.mp hn
      dsimp [S] at hm hn ⊢
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n _
      rfl
    · intro d _ _
      positivity
  have hhi : (∑ n ∈ S.filter (fun n => m < n), ((n - m : ℕ) : ℝ)⁻¹) ≤
      ∑ d ∈ S, (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => n - m)
    · intro n hn k hk heq
      have hn' := (Finset.mem_filter.mp hn).2
      have hk' := (Finset.mem_filter.mp hk).2
      change n - m = k - m at heq
      omega
    · intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hn, hmn⟩ := Finset.mem_filter.mp hn
      dsimp [S] at hn ⊢
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n _
      rfl
    · intro d _ _
      positivity
  have heq : (∑ n ∈ S, if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) =
      (∑ n ∈ S.filter (fun n => n < m), ((m - n : ℕ) : ℝ)⁻¹) +
      ∑ n ∈ S.filter (fun n => m < n), ((n - m : ℕ) : ℝ)⁻¹ := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rcases lt_trichotomy n m with h | h | h
    · simp only [Nat.cast_sub h.le, h, show ¬m < n by omega,
        show m ≠ n by omega, ite_false, ite_true, add_zero, one_div]
      rw [abs_of_pos (sub_pos.mpr (show (n : ℝ) < m by exact_mod_cast h))]
    · subst n
      simp
    · simp only [Nat.cast_sub h.le, h, show ¬n < m by omega,
        show m ≠ n by omega, ite_false, ite_true, zero_add, one_div]
      rw [abs_of_neg (sub_neg.mpr (show (m : ℝ) < n by exact_mod_cast h)), neg_sub]
  change (∑ n ∈ S, _) ≤ _
  rw [heq]
  have hH : (∑ d ∈ S, (d : ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp only [S, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH] at hlo hhi
  linarith

end Sidon
