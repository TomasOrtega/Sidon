module

public import Sidon.NumberTheory.MollifierSeries
public import Sidon.NumberTheory.JensenMollifier
public import Mathlib.NumberTheory.LSeries.Linearity

@[expose] public section

/-! # The balanced mollifier's exact absolutely convergent coefficient series -/

noncomputable section

namespace Sidon

/-- The constant Dirichlet coefficient is removed. -/
def balancedMollifierCoefficient (N n : ℕ) : ℂ :=
  (mollifierCoefficient N n : ℂ) - if n = 1 then 1 else 0

theorem balancedMollifierCoefficient_eq_zero {N n : ℕ} (hnN : n ≤ N) :
    balancedMollifierCoefficient N n = 0 := by
  unfold balancedMollifierCoefficient
  rw [mollifierCoefficient_eq_one_apply hnN]
  split_ifs <;> simp

theorem norm_balancedMollifierCoefficient_le {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ‖balancedMollifierCoefficient N n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hn : n = 1
  · subst n
    rw [balancedMollifierCoefficient_eq_zero hN, norm_zero]
    positivity
  · rw [balancedMollifierCoefficient, if_neg hn, sub_zero, Complex.norm_intCast]
    exact_mod_cast abs_mollifierCoefficient_le N n

theorem LSeriesHasSum_unit_sequence (s : ℂ) :
    LSeriesHasSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s 1 := by
  have hh : HasSum
      (LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s)
      (∑ n ∈ ({1} : Finset ℕ),
        LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [LSeries.term, hn]
  change HasSum (LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s) 1
  simpa [LSeries.term] using hh

/-- Absolute convergence identifies the series with the actual balanced analytic function. -/
theorem LSeriesHasSum_balancedMollifierCoefficient {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    LSeriesHasSum (balancedMollifierCoefficient N) s (mollifierError N s) := by
  have hh := LSeriesHasSum.sub (LSeriesHasSum_mollifierCoefficient hs N) (LSeriesHasSum_unit_sequence s)
  exact hh

end Sidon
