module

public import Sidon.NumberTheory.InghamDensity
public import Sidon.NumberTheory.OptimizedMollifierSlices

@[expose] public section

/-! # An unconditional uniform density estimate for the actual Riemann zeta zeros -/

noncomputable section

namespace Sidon

theorem exists_uniformZetaZeroDensity :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, UniformZetaZeroDensity (23 / 8) 11 C T₀ := by
  obtain ⟨K, hK, T₀, hslices⟩ := exists_optimizedMollifierSlices
  exact exists_uniformZeroDensity_of_mollifier_slices hK hslices

end Sidon
