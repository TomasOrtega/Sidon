module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Tactic

@[expose] public section

/-! # Elementary pole bounds for positive Dirichlet series

The real-series proof is adapted from `RiemannGaussian.ZetaEulerReciprocalAllowance`
at revision `6e969fd6e9c639eed280c595732248c106187603`, using only mathlib.
-/

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem pseries_mass_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hq : -σ < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by change 1 ≤ x at hx; linarith) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ)) 1
    (by simpa only [Nat.cast_one] using ha) (by simpa only [Nat.cast_one] using hi)
    (by intro y hy; simp only [Nat.cast_one, mem_Ioi] at hy
        exact Real.rpow_nonneg (by linarith) _)
  simp only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)] at ht
  simp only [Real.one_rpow, Nat.add_assoc, Nat.reduceAdd] at ht
  have hs := Real.summable_nat_rpow.mpr hq
  rw [← hs.sum_add_tsum_nat_add 2]
  have hzero : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, hzero, Real.one_rpow, zero_add]
  have he : -(1 : ℝ) / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  linarith

/-- A completely uniform bound throughout the half-plane of absolute convergence. -/
theorem norm_riemannZeta_le_pole {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hh := ArithmeticFunction.LSeriesHasSum_zeta hs
  have hsum := hh.summable
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ =
        (n : ℝ) ^ (-s.re) := by
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (show -s.re ≠ 0 by linarith)]
    · rw [LSeries.term, if_neg hn, ArithmeticFunction.zeta_apply_ne hn]
      simp only [Nat.cast_one, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  calc
    _ = ‖∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ := by rw [hh.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := tsum_congr hterm
    _ ≤ _ := pseries_mass_bound hs

end Sidon
