module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace RiemannGaussian.DerivativeRecursionBudget
noncomputable section
open scoped Classical

abbrev Cutoffs := ℕ → ℕ → ℝ → ℝ → ℕ

def shiftCount (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) : ℕ := κ k L ℓ A + 1

theorem shiftCount_pos (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    0 < shiftCount κ k L ℓ A := Nat.zero_lt_succ _

def budget (κ : Cutoffs) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, L, ℓ, A =>
      if 0 < ℓ ∧ ℓ ≤ 1 then
        min (L : ℝ) ((A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
          (3 + 2 * Real.pi))
      else L
  | k + 1, L, ℓ, A =>
      let H := shiftCount κ k L ℓ A
      min (L : ℝ) (Real.sqrt ((((L : ℝ) + H - 1) * ((H : ℝ) * L +
        2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
          budget κ k L (((j : ℝ) + 1) * ℓ) A)) / (H : ℝ) ^ 2))

theorem nonneg (κ : Cutoffs) (k L : ℕ) (ℓ : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ budget κ k L ℓ A := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs with h
    · apply le_min (Nat.cast_nonneg _)
      have hℓ := h.1
      positivity
    · positivity
  | succ k =>
    rw [budget]
    exact le_min (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

theorem le_length (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    budget κ k L ℓ A ≤ L := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs
    · exact min_le_left _ _
    · rfl
  | succ k =>
    rw [budget]
    exact min_le_left _ _

theorem base_le (κ : Cutoffs) (L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget κ 0 L ℓ A ≤
      (A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
        (3 + 2 * Real.pi) := by
  rw [budget]
  by_cases hℓ1 : ℓ ≤ 1
  · rw [ite_eq_left ⟨hℓ, hℓ1⟩]
    exact min_le_right _ _
  · rw [ite_eq_right (fun h ↦ hℓ1 h.2)]
    have hs1 : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.mpr (by linarith)
    have hA0 : 0 ≤ A := by linarith
    have hL : (L : ℝ) ≤ A * L := by nlinarith [Nat.cast_nonneg (α := ℝ) L]
    have hp := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hA0 (Nat.cast_nonneg (α := ℝ) L))
    simp only [mul_one] at hp
    calc
      _ ≤ A * L * Real.sqrt ℓ := hL.trans hp
      _ = (A * L * Real.sqrt ℓ / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul
        · exact le_add_of_nonneg_right (by positivity)
        · linarith
        · positivity
        · positivity

end
end RiemannGaussian.DerivativeRecursionBudget
