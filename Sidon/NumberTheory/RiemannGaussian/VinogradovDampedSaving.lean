module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovDamping

@[expose] public section

namespace RiemannGaussian.VinogradovDampedSaving
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovKorobovBlock RiemannGaussian.VinogradovKorobovDamping
theorem abelTransform_norm_affine_le (w : ℕ → ℝ) (F : ℕ → ℂ) (N : ℕ) {E D : ℝ}
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N))
    (hF : ∀ n ≤ N, ‖F (n + 1)‖ ≤ (n + 1 : ℕ) * E + D) :
    ‖abelTransform (fun n => (w n : ℂ)) F N‖ ≤
      E * (∑ n ∈ Finset.range (N + 1), w n) + D * w 0 := by
  have hd (n : ℕ) (hn : n < N) : 0 ≤ w n - w (n + 1) := by
    exact sub_nonneg.mpr (hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  unfold abelTransform
  calc
    _ ≤ ‖(w N : ℂ) * F (N + 1)‖ +
        ∑ n ∈ Finset.range N, ‖((w n : ℂ) - (w (n + 1) : ℂ)) * F (n + 1)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w N * ((N + 1 : ℕ) * E + D) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * ((n + 1 : ℕ) * E + D) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N le_rfl)]
        exact mul_le_mul_of_nonneg_left (hF N le_rfl) (hw N le_rfl)
      · apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hd n hn')]
        exact mul_le_mul_of_nonneg_left (hF n hn'.le) (hd n hn')
    _ = E * (w N * (N + 1 : ℕ) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * (n + 1 : ℕ)) +
        D * (w N + ∑ n ∈ Finset.range N, (w n - w (n + 1))) := by
      have he (n : ℕ) : (w n - w (n + 1)) * ((n + 1 : ℕ) * E + D) =
          E * ((w n - w (n + 1)) * (n + 1 : ℕ)) + D * (w n - w (n + 1)) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = _ := by rw [abel_length_mass, Finset.sum_range_sub']; ring

end
end RiemannGaussian.VinogradovDampedSaving
