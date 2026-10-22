import Sidon.Analysis.Approximation.Polynomial
import Mathlib.LinearAlgebra.Lagrange

/-! # Finite real interpolation of bounded circle frequencies -/

noncomputable section

open scoped BigOperators Classical ComplexConjugate
open Complex

namespace Sidon.BandwidthCounterexample

private theorem fourier_natCast_eq_pow (k : ℕ) (x : AddCircle (1 : ℝ)) :
    fourier (k : ℤ) x = fourier 1 x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem exists_complex_interpolation_weights (M : ℕ)
    (t : Fin (2 * M + 1) → AddCircle (1 : ℝ)) (ht : Function.Injective t) :
    ∃ b : Fin (2 * M + 1) → ℂ, ∀ n : ℤ, |n| ≤ M →
      (∑ j, b j * fourier n (t j)) = 1 := by
  let z : Fin (2 * M + 1) → ℂ := fun j => fourier 1 (t j)
  have hz : Function.Injective z := by
    intro i j hij
    apply ht
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.coe_injective
    simpa only [z, fourier_one] using hij
  let b : Fin (2 * M + 1) → ℂ := fun j =>
    (Lagrange.basis Finset.univ z j).eval 1 * fourier (M : ℤ) (t j)
  refine ⟨b, ?_⟩
  intro n hn
  have hnlo : -(M : ℤ) ≤ n := (abs_le.mp hn).1
  have hnhi : n ≤ M := (abs_le.mp hn).2
  let k := (n + M).toNat
  have hkcast : (k : ℤ) = n + M := Int.toNat_of_nonneg (by omega)
  have hklt : k < 2 * M + 1 := by omega
  have hp : (Polynomial.X ^ k : Polynomial ℂ) =
      Lagrange.interpolate Finset.univ z
        (fun j => (Polynomial.X ^ k : Polynomial ℂ).eval (z j)) := by
    apply Lagrange.eq_interpolate
    · exact hz.injOn
    · simpa only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin,
        Nat.cast_lt] using hklt
  have heval := congrArg (Polynomial.eval (1 : ℂ)) hp
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C] at heval
  calc
    (∑ j, b j * fourier n (t j)) =
        ∑ j, z j ^ k * (Lagrange.basis Finset.univ z j).eval 1 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← fourier_natCast_eq_pow, hkcast, fourier_add]
      dsimp [b, z]
      ring
    _ = 1 := heval.symm

theorem exists_real_interpolation_weights (M : ℕ)
    (t : Fin (2 * M + 1) → AddCircle (1 : ℝ)) (ht : Function.Injective t) :
    ∃ b : Fin (2 * M + 1) → ℝ, ∀ n : ℤ, |n| ≤ M →
      (∑ j, (b j : ℂ) * fourier n (t j)) = 1 := by
  obtain ⟨b, hb⟩ := exists_complex_interpolation_weights M t ht
  refine ⟨fun j => (b j).re, ?_⟩
  intro n hn
  have hp := hb n hn
  have hm := congrArg (starRingEnd ℂ) (hb (-n) (by simpa using hn))
  simp only [map_sum, map_mul, fourier_neg, starRingEnd_apply,
    star_star, map_one] at hm
  have hterm (j : Fin (2 * M + 1)) :
      (b j).re * fourier n (t j) =
        (b j * fourier n (t j) + conj (b j) * fourier n (t j)) / 2 := by
    rw [← add_mul, Complex.add_conj]
    push_cast
    ring
  simp_rw [hterm, starRingEnd_apply]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hp, hm]
  norm_num

theorem exists_nodes_away_from_zero (L : ℕ) :
    ∃ t : Fin L → AddCircle (1 : ℝ), Function.Injective t ∧
      ∀ j, (1 : ℝ) / 4 ≤ ‖t j‖ := by
  let r : Fin L → ℝ := fun j => 1 / 4 + (j : ℝ) / (4 * ((L : ℝ) + 1))
  have hden : (0 : ℝ) < 4 * ((L : ℝ) + 1) := by positivity
  have hrlo (j : Fin L) : (1 : ℝ) / 4 ≤ r j := by
    dsimp [r]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hden.le)
  have hrhi (j : Fin L) : r j < 1 / 2 := by
    have hj : (j : ℝ) < (L : ℝ) + 1 := by exact_mod_cast (by omega : j.val < L + 1)
    have hh : (j : ℝ) / (4 * ((L : ℝ) + 1)) < 1 / 4 :=
      (div_lt_iff₀ hden).mpr (by nlinarith)
    dsimp [r]
    linarith
  have hrmem (j : Fin L) : r j ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    exact ⟨by linarith [hrlo j], by linarith [hrhi j]⟩
  refine ⟨fun j => (r j : AddCircle (1 : ℝ)), ?_, ?_⟩
  · intro i j hij
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hrmem i) (hrmem j)).mp hij
    have heq' : (i : ℝ) / (4 * ((L : ℝ) + 1)) =
        (j : ℝ) / (4 * ((L : ℝ) + 1)) := by simpa only [r, add_right_inj] using heq
    have heq'' : (i : ℝ) = (j : ℝ) := (div_left_inj' (ne_of_gt hden)).mp heq'
    apply Fin.ext
    exact_mod_cast heq''
  · intro j
    have hr0 : 0 ≤ r j := by linarith [hrlo j]
    have hn : ‖(r j : AddCircle (1 : ℝ))‖ = |r j| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by
        simpa only [abs_one, abs_of_nonneg hr0] using (hrhi j).le)
    rw [hn, abs_of_nonneg hr0]
    exact hrlo j

theorem exists_real_interpolation_away_from_zero (M : ℕ) :
    ∃ t : Fin (2 * M + 1) → AddCircle (1 : ℝ),
      (∀ j, (1 : ℝ) / 4 ≤ ‖t j‖) ∧
      ∃ b : Fin (2 * M + 1) → ℝ, ∀ n : ℤ, |n| ≤ M →
        (∑ j, (b j : ℂ) * fourier n (t j)) = 1 := by
  obtain ⟨t, ht, haway⟩ := exists_nodes_away_from_zero (2 * M + 1)
  obtain ⟨b, hb⟩ := exists_real_interpolation_weights M t ht
  exact ⟨t, haway, b, hb⟩

end Sidon.BandwidthCounterexample
