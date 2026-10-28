module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBlock

@[expose] public section

namespace RiemannGaussian.VinogradovDirichletSaving
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovKorobovBlock
theorem block_bound_of_product_bound {M L : ℕ} (hM : 0 < M) {z : ℝ} (hz : 0 < z)
    (t K : ℝ)
    (hK : ∀ n ∈ Finset.range L,
      ‖∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        dirichletTerm t (z + n) ((a.val + 1) * b)‖ ≤ K) :
    ‖block (dirichletTerm t z) L‖ ≤ (L : ℝ) * K / (M : ℝ) ^ 2 + 2 * (M : ℝ) ^ 2 := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let A := (Finset.univ : Finset (Fin M)) ×ˢ Finset.Icc 1 M
  have h := weighted_shift_identity A (fun p => (p.1.val + 1) * p.2)
    (fun _ => 1) (dirichletTerm t z) L
  have he : ((M : ℂ) * M) * block (dirichletTerm t z) L =
      (∑ n ∈ Finset.range L, ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        dirichletTerm t (z + n) ((a.val + 1) * b)) +
      ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
        boundary (dirichletTerm t z) L ((a.val + 1) * b) := by
    have hshift (n p : ℕ) : dirichletTerm t z (n + p) = dirichletTerm t (z + n) p := by
      simp only [dirichletTerm, Nat.cast_add, add_assoc]
    simpa only [A, Finset.sum_product, Finset.sum_const, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, Nat.cast_mul, mul_one, one_mul, hshift] using h
  have hsum : ‖∑ n ∈ Finset.range L, ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
      dirichletTerm t (z + n) ((a.val + 1) * b)‖ ≤ (L : ℝ) * K := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _n ∈ Finset.range L, K := Finset.sum_le_sum hK
      _ = _ := by simp
  have hb : ‖∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
      boundary (dirichletTerm t z) L ((a.val + 1) * b)‖ ≤ 2 * (M : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ a : Fin M, ∑ b ∈ Finset.Icc 1 M,
          ‖boundary (dirichletTerm t z) L ((a.val + 1) * b)‖ := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : Fin M, ∑ _b ∈ Finset.Icc 1 M, 2 * (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b hb
        apply (boundary_norm_le (dirichletTerm t z)
          (fun n => (norm_dirichletTerm hz t n).le) L ((a.val + 1) * b)).trans
        have ha : ((a.val + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast a.isLt
        have hb' : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hb).2
        have hp := mul_le_mul ha hb' (Nat.cast_nonneg b) hMr.le
        push_cast at hp ⊢
        nlinarith only [hp]
      _ = _ := by simp; ring
  have hnorm : (M : ℝ) ^ 2 * ‖block (dirichletTerm t z) L‖ ≤
      (L : ℝ) * K + 2 * (M : ℝ) ^ 4 := by
    calc
      _ = ‖((M : ℂ) * M) * block (dirichletTerm t z) L‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast, ← pow_two]
      _ = _ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsum hb)
  calc
    _ ≤ ((L : ℝ) * K + 2 * (M : ℝ) ^ 4) / (M : ℝ) ^ 2 :=
      (le_div_iff₀ (pow_pos hMr 2)).mpr (by simpa only [mul_comm] using hnorm)
    _ = _ := by field_simp

end
end RiemannGaussian.VinogradovDirichletSaving
