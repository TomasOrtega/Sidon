import Sidon.Analysis.FiniteFourier
import Sidon.Combinatorics.Energy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Haar orthogonality and Parseval for finite integer Fourier sums -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

/-- Probability Haar measure on the period-one circle. -/
abbrev circleHaar : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle

theorem integral_conj_fourier_mul (m n : ℤ) :
    (∫ α : AddCircle (1 : ℝ), conj (fourier m α) * fourier n α ∂circleHaar) =
      if m = n then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) m n
  rw [ContinuousMap.inner_toLp circleHaar (fourier m) (fourier n)] at h
  simpa only [mul_comm] using h

theorem integral_fourier (n : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourier n α ∂circleHaar) = if n = 0 then 1 else 0 := by
  simpa only [fourier_zero, map_one, one_mul, eq_comm] using integral_conj_fourier_mul 0 n

theorem toLp_fourierSum (f : ℤ →₀ ℂ) :
    ContinuousMap.toLp (E := ℂ) 2 circleHaar ℂ (fourierSum f) =
      Finsupp.linearCombination ℂ (fourierLp (T := 1) 2) f := by
  simp only [fourierSum, Finsupp.sum, map_sum, _root_.map_smul, Finsupp.linearCombination_apply]

theorem integral_conj_fourierSum_mul (f g : ℤ →₀ ℂ) :
    (∫ α : AddCircle (1 : ℝ), conj (fourierSum f α) * fourierSum g α ∂circleHaar) =
      f.sum (fun n c => conj c * g n) := by
  simp_rw [mul_comm (conj _)]
  rw [← ContinuousMap.inner_toLp circleHaar (fourierSum f) (fourierSum g),
    toLp_fourierSum, toLp_fourierSum]
  simpa only [mul_comm] using (orthonormal_fourier (T := 1)).inner_finsupp_eq_sum_left f g

theorem integral_norm_fourierSum_sq (f : ℤ →₀ ℂ) :
    (∫ α : AddCircle (1 : ℝ), ‖fourierSum f α‖ ^ 2 ∂circleHaar) =
      f.sum (fun _ c => ‖c‖ ^ 2) := by
  have h := integral_conj_fourierSum_mul f f
  simp only [Finsupp.sum, Complex.conj_mul', ← Complex.ofReal_pow] at h
  apply Complex.ofReal_injective
  calc
    ((∫ α : AddCircle (1 : ℝ), ‖fourierSum f α‖ ^ 2 ∂circleHaar : ℝ) : ℂ) =
        ∫ α : AddCircle (1 : ℝ), ((‖fourierSum f α‖ ^ 2 : ℝ) : ℂ) ∂circleHaar :=
      (integral_ofReal (𝕜 := ℂ) (μ := circleHaar)
        (f := fun α => ‖fourierSum f α‖ ^ 2)).symm
    _ = _ := h
    _ = _ := by simp [Finsupp.sum]

theorem integral_norm_fourierSum_indicator_sq (s : Finset ℤ) :
    (∫ α : AddCircle (1 : ℝ), ‖fourierSum (indicatorFinsupp s) α‖ ^ 2 ∂circleHaar) =
      (s.card : ℝ) := by
  rw [integral_norm_fourierSum_sq, Finsupp.sum, support_indicatorFinsupp]
  calc
    ∑ n ∈ s, ‖indicatorFinsupp s n‖ ^ 2 = ∑ _ ∈ s, (1 : ℝ) :=
      Finset.sum_congr rfl fun n hn => by rw [indicatorFinsupp_apply, if_pos hn, norm_one, one_pow]
    _ = _ := by simp

theorem integral_conj_sum_fourier_mul_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (m : ι → ℤ) (n : κ → ℤ) :
    (∫ α : AddCircle (1 : ℝ),
      conj (∑ i ∈ s, fourier (m i) α) * ∑ j ∈ t, fourier (n j) α ∂circleHaar) =
      ∑ i ∈ s, ∑ j ∈ t, if m i = n j then (1 : ℂ) else 0 := by
  have h : (∫ α : AddCircle (1 : ℝ),
      conj ((∑ i ∈ s, fourier (T := 1) (m i)) α) *
        (∑ j ∈ t, fourier (T := 1) (n j)) α ∂circleHaar) =
        ∑ i ∈ s, ∑ j ∈ t, if m i = n j then (1 : ℂ) else 0 := by
    simp_rw [mul_comm (conj _)]
    rw [← ContinuousMap.inner_toLp circleHaar (∑ i ∈ s, fourier (m i))
      (∑ j ∈ t, fourier (n j)), map_sum, map_sum]
    simp only [sum_inner, inner_sum, orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))]
    rw [Finset.sum_comm]
  simpa only [ContinuousMap.sum_apply] using h

theorem fourierSum_indicator_sq (s : Finset ℤ) (α : AddCircle (1 : ℝ)) :
    fourierSum (indicatorFinsupp s) α ^ 2 =
      ∑ p ∈ s ×ˢ s, fourier (p.1 + p.2) α := by
  rw [pow_two, fourierSum_indicatorFinsupp_apply, Finset.sum_mul_sum]
  simp only [Finset.sum_product, fourier_add]

theorem integral_norm_fourierSum_indicator_fourth (s : Finset ℤ) :
    (∫ α : AddCircle (1 : ℝ), ‖fourierSum (indicatorFinsupp s) α‖ ^ 4 ∂circleHaar) =
      (Finset.addEnergy s s : ℝ) := by
  have h := integral_conj_sum_fourier_mul_sum (s ×ˢ s) (s ×ˢ s)
    (fun p => p.1 + p.2) (fun p => p.1 + p.2)
  simp_rw [← fourierSum_indicator_sq, Complex.conj_mul', ← Complex.ofReal_pow,
    norm_pow, ← pow_mul, show 2 * 2 = 4 from rfl] at h
  have hcount : (∑ i ∈ s ×ˢ s, ∑ j ∈ s ×ˢ s,
      if i.1 + i.2 = j.1 + j.2 then (1 : ℂ) else 0) = (Finset.addEnergy s s : ℂ) := by
    rw [Finset.addEnergy_eq_card_filter, Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_product]
  rw [hcount] at h
  apply Complex.ofReal_injective
  calc
    ((∫ α : AddCircle (1 : ℝ), ‖fourierSum (indicatorFinsupp s) α‖ ^ 4
        ∂circleHaar : ℝ) : ℂ) =
      ∫ α : AddCircle (1 : ℝ), ((‖fourierSum (indicatorFinsupp s) α‖ ^ 4 : ℝ) : ℂ)
        ∂circleHaar := (integral_ofReal (𝕜 := ℂ) (μ := circleHaar)
          (f := fun α => ‖fourierSum (indicatorFinsupp s) α‖ ^ 4)).symm
    _ = _ := h
    _ = _ := by simp

theorem integral_norm_fourierSum_sidon_fourth {s : Finset ℤ}
    (hs : IsSidonSet (s : Set ℤ)) :
    (∫ α : AddCircle (1 : ℝ), ‖fourierSum (indicatorFinsupp s) α‖ ^ 4 ∂circleHaar) =
      2 * (s.card : ℝ) ^ 2 - s.card := by
  rw [integral_norm_fourierSum_indicator_fourth, hs.addEnergy_eq]
  have hcard : s.card ≤ 2 * s.card ^ 2 := by
    nlinarith [Nat.le_mul_self s.card]
  rw [Nat.cast_sub hcard]
  norm_cast

end Sidon
