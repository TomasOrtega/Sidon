module

public import Sidon.Transference.Counting
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-! # Weighted Fourier moments for Sidon majorants -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Sidon

def weightedFourier (A : Finset ℤ) (f : ℤ → ℝ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑ n ∈ A, (f n : ℂ) • fourier n

theorem weightedFourier_apply (A : Finset ℤ) (f : ℤ → ℝ) (α : AddCircle (1 : ℝ)) :
    weightedFourier A f α = ∑ n ∈ A, (f n : ℂ) * fourier n α := by
  simp only [weightedFourier, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

theorem conj_weightedFourier_apply (A : Finset ℤ) (f : ℤ → ℝ) (α : AddCircle (1 : ℝ)) :
    conj (weightedFourier A f α) = ∑ n ∈ A, (f n : ℂ) * fourier (-n) α := by
  simp only [weightedFourier_apply, map_sum, map_mul, Complex.conj_ofReal, fourier_neg]

theorem weightedFourier_one (A : Finset ℤ) :
    weightedFourier A (fun _ => 1) = fourierSum (indicatorFinsupp A) := by
  ext α
  simp only [weightedFourier_apply, Complex.ofReal_one, one_mul,
    fourierSum_indicatorFinsupp_apply]

theorem norm_weightedFourier_apply_le (A : Finset ℤ) (f : ℤ → ℝ) (α : AddCircle (1 : ℝ)) :
    ‖weightedFourier A f α‖ ≤ ∑ n ∈ A, |f n| := by
  rw [weightedFourier_apply]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖fourier n α‖ = 1 from Circle.norm_coe _,
    mul_one]

theorem weightedSolutionCount_ofReal {ι : Type*} [Fintype ι]
    (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → ℝ) :
    weightedSolutionCount A c (fun i n => (f i n : ℂ)) =
      ((weightedSolutionCount A c f : ℝ) : ℂ) := by
  simp only [weightedSolutionCount, Complex.ofReal_sum, Complex.ofReal_prod]

theorem fourth_product_weightedFourier (A : Finset ℤ) (f : ℤ → ℝ)
    (α : AddCircle (1 : ℝ)) :
    (∏ i : Fin 4, ∑ n ∈ A, (f n : ℂ) * fourier (![1, 1, -1, -1] i * n) α) =
      ((‖weightedFourier A f α‖ ^ 4 : ℝ) : ℂ) := by
  rw [Fin.prod_univ_four]
  change (∑ n ∈ A, (f n : ℂ) * fourier (1 * n) α) *
    (∑ n ∈ A, (f n : ℂ) * fourier (1 * n) α) *
    (∑ n ∈ A, (f n : ℂ) * fourier (-1 * n) α) *
    (∑ n ∈ A, (f n : ℂ) * fourier (-1 * n) α) = _
  simp only [one_mul, neg_one_mul]
  rw [← weightedFourier_apply, ← conj_weightedFourier_apply]
  calc
    _ = (conj (weightedFourier A f α) * weightedFourier A f α) ^ 2 := by ring
    _ = _ := by
      rw [Complex.conj_mul']
      push_cast
      ring

theorem integral_norm_weightedFourier_fourth (A : Finset ℤ) (f : ℤ → ℝ) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier A f α‖ ^ 4 ∂circleHaar) =
      weightedSolutionCount A (![1, 1, -1, -1] : Fin 4 → ℤ) (fun _ n => f n) := by
  apply Complex.ofReal_injective
  rw [← weightedSolutionCount_ofReal]
  calc
    _ = ∫ α : AddCircle (1 : ℝ), ((‖weightedFourier A f α‖ ^ 4 : ℝ) : ℂ) ∂circleHaar :=
      (integral_ofReal (𝕜 := ℂ) (μ := circleHaar)
        (f := fun α => ‖weightedFourier A f α‖ ^ 4)).symm
    _ = ∫ α : AddCircle (1 : ℝ),
        ∏ i : Fin 4, ∑ n ∈ A, (f n : ℂ) * fourier (![1, 1, -1, -1] i * n) α ∂circleHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun α => (fourth_product_weightedFourier A f α).symm
    _ = _ := integral_prod_expanded_fourier _ _ _

theorem integral_norm_weightedFourier_fourth_le {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (f : ℤ → ℝ) {a : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hfa : ∀ n, f n ≤ a) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier S f α‖ ^ 4 ∂circleHaar) ≤
      a ^ 4 * (2 * (S.card : ℝ) ^ 2) := by
  rw [integral_norm_weightedFourier_fourth]
  have hmono := weightedSolutionCount_mono S (![1, 1, -1, -1] : Fin 4 → ℤ)
    (fun _ n => f n) (fun _ _ => a) (fun _ n => hf0 n) (fun _ n => hfa n)
  have heq : weightedSolutionCount S (![1, 1, -1, -1] : Fin 4 → ℤ) (fun _ _ => a) =
      a ^ 4 * (2 * (S.card : ℝ) ^ 2 - S.card) := by
    have h := weightedSolutionCount_const_mul S (![1, 1, -1, -1] : Fin 4 → ℤ)
      (fun _ _ => (1 : ℝ)) a
    simp only [mul_one, Fintype.card_fin] at h
    rw [h, ← integral_norm_weightedFourier_fourth, weightedFourier_one,
      integral_norm_fourierSum_sidon_fourth hS]
  rw [heq] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (by positivity))

end Sidon
