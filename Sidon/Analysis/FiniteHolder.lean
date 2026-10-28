module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! # Equal-moment bounds for a finite product -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

theorem prod_le_average_powers {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (u : ι → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) :
    ∏ i ∈ s, u i ≤ (∑ i ∈ s, u i ^ s.card) / s.card := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hh := Real.geom_mean_le_arith_mean_weighted s
    (fun _ => (s.card : ℝ)⁻¹) (fun i => u i ^ s.card)
    (fun _ _ => by positivity) hw (fun i hi => pow_nonneg (hu i hi) _)
  have heq : (∏ i ∈ s, (u i ^ s.card) ^ (s.card : ℝ)⁻¹) = ∏ i ∈ s, u i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.pow_rpow_inv_natCast (hu i hi) hs.card_ne_zero
  rw [heq, ← Finset.mul_sum] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem integral_prod_le_of_equal_moments {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (hs : s.Nonempty) (f : ι → α → ℝ) {B : ℝ}
    (hf0 : ∀ i ∈ s, ∀ x, 0 ≤ f i x)
    (hprod : Integrable (fun x => ∏ i ∈ s, f i x) μ)
    (hpowers : ∀ i ∈ s, Integrable (fun x => f i x ^ s.card) μ)
    (hB : ∀ i ∈ s, (∫ x, f i x ^ s.card ∂μ) ≤ B) :
    (∫ x, ∏ i ∈ s, f i x ∂μ) ≤ B := by
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  calc
    _ ≤ ∫ x, (∑ i ∈ s, f i x ^ s.card) / s.card ∂μ := by
      apply integral_mono hprod ((integrable_finsetSum s hpowers).div_const _)
      intro x
      exact prod_le_average_powers s hs (fun i => f i x) (fun i hi => hf0 i hi x)
    _ = (∑ i ∈ s, ∫ x, f i x ^ s.card ∂μ) / s.card := by
      rw [integral_div, integral_finsetSum s hpowers]
    _ ≤ B := by
      apply (div_le_iff₀ hcard).mpr
      have hh := Finset.sum_le_sum hB
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hh

end Sidon
