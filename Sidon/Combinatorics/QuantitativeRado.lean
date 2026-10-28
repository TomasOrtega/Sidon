module

public import Sidon.Combinatorics.QuantitativeRado.Assembly
public import Sidon.Combinatorics.QuantitativeRado.KernelMatrix

@[expose] public section

/-! # Quantitative Rado theorem for one homogeneous equation -/

namespace Sidon.QuantitativeRado

theorem exists_many_monochromatic_linearSolutions {s r : ℕ}
    (hs : 2 ≤ s) (hr : 0 < r) (a : Fin s → ℤ) (ha : ∀ i, a i ≠ 0)
    (I : Finset (Fin s)) (hIne : I.Nonempty) (hI : ∑ i ∈ I, a i = 0) :
    ∃ N₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
        δ * (N : ℝ) ^ (s - 1) ≤
          (linearSolutions ((interval N).filter (fun x => χ x = colour)) a).card := by
  obtain ⟨p, c, hp, hc, B, hBinj, hBzero, hBpattern⟩ :=
    exists_deuber_kernel_matrix hs a ha I hIne hI
  exact exists_many_monochromatic_of_pattern_map (by omega) hr p c hp hc a
    B.mulVec hBinj hBpattern hBzero

end Sidon.QuantitativeRado
