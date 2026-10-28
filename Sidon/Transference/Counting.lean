module

public import Sidon.Analysis.FourierIntegral
public import Sidon.Combinatorics.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Finite weighted counts for one homogeneous linear equation -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

variable {ι : Type*} [Fintype ι]

def linearSolutions (A : Finset ℤ) (c : ι → ℤ) : Finset (ι → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => A).filter fun x => ∑ i, c i * x i = 0

@[simp]
theorem mem_linearSolutions (A : Finset ℤ) (c : ι → ℤ) (x : ι → ℤ) :
    x ∈ linearSolutions A c ↔ (∀ i, x i ∈ A) ∧ ∑ i, c i * x i = 0 := by
  classical
  simp [linearSolutions, Fintype.mem_piFinset]

def weightedSolutionCount {R : Type*} [CommSemiring R]
    (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → R) : R :=
  ∑ x ∈ linearSolutions A c, ∏ i, f i (x i)

theorem weightedSolutionCount_nonneg (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) : 0 ≤ weightedSolutionCount A c f := by
  exact Finset.sum_nonneg fun x _ => Finset.prod_nonneg fun i _ => hf i (x i)

theorem weightedSolutionCount_mono (A : Finset ℤ) (c : ι → ℤ)
    (f g : ι → ℤ → ℝ) (hf : ∀ i x, 0 ≤ f i x)
    (hfg : ∀ i x, f i x ≤ g i x) :
    weightedSolutionCount A c f ≤ weightedSolutionCount A c g := by
  apply Finset.sum_le_sum
  intro x _
  exact Finset.prod_le_prod₀ (fun i _ => hf i (x i)) (fun i _ => hfg i (x i))

theorem weightedSolutionCount_const_mul {R : Type*} [CommSemiring R]
    (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → R) (a : R) :
    weightedSolutionCount A c (fun i x => a * f i x) =
      a ^ Fintype.card ι * weightedSolutionCount A c f := by
  simp only [weightedSolutionCount, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Finset.mul_sum]

theorem prod_fourier_eq_fourier_sum (n : ι → ℤ) (α : AddCircle (1 : ℝ)) :
    ∏ i, fourier (n i) α = fourier (∑ i, n i) α := by
  classical
  have h (s : Finset ι) : ∏ i ∈ s, fourier (n i) α = fourier (∑ i ∈ s, n i) α := by
    induction s using Finset.induction with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, fourier_zero, ContinuousMap.one_apply]
    | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, fourier_add, ih]
  exact h Finset.univ

theorem integral_prod_expanded_fourier (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → ℂ) :
    (∫ α : AddCircle (1 : ℝ), ∏ i, ∑ n ∈ A, f i n * fourier (c i * n) α ∂circleHaar) =
      weightedSolutionCount A c f := by
  classical
  simp_rw [Finset.prod_univ_sum]
  rw [integral_finset_sum]
  · unfold weightedSolutionCount linearSolutions
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [Finset.prod_mul_distrib, prod_fourier_eq_fourier_sum]
    rw [integral_const_mul, integral_fourier]
    split_ifs <;> simp
  · intro x _
    exact (show Continuous (fun α : AddCircle (1 : ℝ) =>
      ∏ i, f i (x i) * fourier (c i * x i) α) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Sidon
