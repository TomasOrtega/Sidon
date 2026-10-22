import Sidon.Transference.Counting

/-! # Indicator weights count finite solutions -/

noncomputable section

namespace Sidon

variable {ι : Type*} [Fintype ι]

theorem weightedSolutionCount_indicator (A C : Finset ℤ) (hCA : C ⊆ A) (c : ι → ℤ) :
    weightedSolutionCount A c (fun _ n => if n ∈ C then (1 : ℝ) else 0) =
      (linearSolutions C c).card := by
  classical
  unfold weightedSolutionCount
  simp only [Finset.prod_boole, Finset.mem_univ, forall_const, Finset.sum_boole]
  congr 2
  ext x
  simp only [Finset.mem_filter, mem_linearSolutions]
  constructor
  · rintro ⟨⟨_, heq⟩, hxC⟩
    exact ⟨hxC, heq⟩
  · rintro ⟨hxC, heq⟩
    exact ⟨⟨fun i => hCA (hxC i), heq⟩, hxC⟩

theorem weightedSolutionCount_scaled_indicator (A C : Finset ℤ) (hCA : C ⊆ A)
    (c : ι → ℤ) (a : ℝ) :
    weightedSolutionCount A c (fun _ n => a * if n ∈ C then (1 : ℝ) else 0) =
      a ^ Fintype.card ι * (linearSolutions C c).card := by
  rw [weightedSolutionCount_const_mul, weightedSolutionCount_indicator A C hCA c]

end Sidon
