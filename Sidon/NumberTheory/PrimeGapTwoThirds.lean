module

public import Sidon.NumberTheory.PrimeGapFromDensity
public import Sidon.NumberTheory.PrimeIntervals
public import Sidon.NumberTheory.ZetaDensity

@[expose] public section

/-! An unconditional prime in every sufficiently large interval of length O(x^(2/3)). -/

noncomputable section

namespace Sidon

theorem exists_primeIntervalBound_two_thirds :
    ∃ X : ℝ, PrimeIntervalBound ((2 : ℝ) / 3) 128 X := by
  obtain ⟨C, hC, T₀, hdensity⟩ := exists_uniformZetaZeroDensity
  have hevent := eventually_prime_interval_of_uniform_zero_density
    (by norm_num : (0 : ℝ) ≤ 23 / 8) hC.le
    (by norm_num : (23 : ℝ) / 8 < 50 / 17) hdensity
  simpa only [PrimeIntervalBound] using Filter.eventually_atTop.mp hevent

end Sidon
