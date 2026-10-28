module

public import Sidon.Constructions.Extremal
public import Sidon.NumberTheory.PrimeGapTwoThirds

@[expose] public section

/-! # The unconditional Fourier rate for maximum Sidon sets -/

noncomputable section

namespace Sidon

/-- Corollary 1.4, with its prime-interval input proved in the project. -/
theorem largest_sidon_fourier_uniformity :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, IsMaximumSidon N S →
      ‖fourierSum (indicatorFinsupp S) -
        ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
        K * ‖fourierSum (indicatorFinsupp S)‖ * (N : ℝ) ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨X, hgap⟩ := exists_primeIntervalBound_two_thirds
  exact largest_sidon_fourier_uniformity_of_prime_interval (by norm_num : (0 : ℝ) ≤ 128) hgap

end Sidon
