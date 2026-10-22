import Sidon.Equidistribution.BohrCutoffs
import Sidon.Analysis.BohrOptimization

/-! # From smooth orbit estimates to regular Bohr-set equidistribution -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem regular_bohr_equidistribution_of_smooth {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (S : Finset ℤ) (hSN : S ⊆ interval N) (hS : S.Nonempty)
    (α : Fin d → AddCircle (1 : ℝ)) {ρ E C : ℝ} (hρ : 0 < ρ)
    (hreg : IsRegularBohrSet N α ρ) (hE : 0 < E) (hC : 1 ≤ C)
    (hsmooth : ∀ (K : ℝ), 1 ≤ K → ∀ F : (Fin d → AddCircle (1 : ℝ)) → ℝ,
      (∀ β, 0 ≤ F β) → (∀ β, F β ≤ 1) → LipschitzWith (Real.toNNReal K) F →
      |(𝔼 x ∈ S, F (x • α)) - (𝔼 x ∈ interval N, F (x • α))| ≤
        C * K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ)))) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤
      (100 + C) * ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) := by
  by_cases hρhalf : 1 / 2 ≤ ρ
  · rw [bohrSet_eq_interval_of_half_le N α hρhalf, Finset.inter_eq_left.mpr hSN,
      card_interval, div_self (by exact_mod_cast hS.card_ne_zero : (S.card : ℝ) ≠ 0),
      div_self (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), sub_self, abs_zero]
    positivity
  · apply regular_bohr_optimization hd (bohr_discrepancy_le_one N S α ρ) hC hE hρ
      (le_of_not_ge hρhalf)
    intro t ht hsmall
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hsmall' := (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * d)).mp hsmall
    have htone : t ≤ 1 := by nlinarith
    have hK : 1 ≤ t⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ ht).mpr (by simpa only [one_mul] using htone)
    apply hreg.discrepancy_le_cutoff_errors S hSN hN hd hρ ht hsmall
    · exact hsmooth t⁻¹ hK (clippedNormRamp (ρ + t) t)
        (clippedNormRamp_nonneg (ρ + t) t) (clippedNormRamp_le_one (ρ + t) t)
        (lipschitzWith_clippedNormRamp (ρ + t) ht)
    · exact hsmooth t⁻¹ hK (clippedNormRamp ρ t)
        (clippedNormRamp_nonneg ρ t) (clippedNormRamp_le_one ρ t)
        (lipschitzWith_clippedNormRamp ρ ht)

end Sidon
