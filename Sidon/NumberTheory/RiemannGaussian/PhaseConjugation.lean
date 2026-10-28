module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.PhaseIncrementInverse

@[expose] public section

namespace RiemannGaussian.PhaseConjugation
noncomputable section
open RiemannGaussian.PhaseIncrementInverse
open scoped Classical

theorem rotation_neg (x : ℝ) :
    rotation (-x) = starRingEnd ℂ (rotation x) := by
  simp only [PhaseIncrementInverse.rotation, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

theorem norm_sum_neg {ι : Type*} (S : Finset ι) (φ : ι → ℝ) :
    ‖∑ n ∈ S, rotation (-φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  simp only [rotation_neg, ← map_sum, Complex.norm_conj]

theorem norm_sum_neg_one_pow {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (k : ℕ) :
    ‖∑ n ∈ S, rotation ((-1 : ℝ) ^ k * φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    simp only [pow_succ, mul_neg_one, neg_mul]
    rw [norm_sum_neg]
    exact ih

theorem neg_one_pow_mul_self (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  simpa only [mul_pow, one_pow] using
    congrArg (fun x : ℝ ↦ x ^ k) (show (-1 : ℝ) * -1 = 1 by norm_num)

end
end RiemannGaussian.PhaseConjugation
