module

public import Sidon.Analysis.FourierIntegral
public import Sidon.Analysis.Correlation
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! # Fourier tests and arithmetic progression sums -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

/-- The `L¹` norm of a finite Fourier sum under probability Haar measure. -/
def fourierL1 (f : ℤ →₀ ℂ) : ℝ :=
  ∫ α : AddCircle (1 : ℝ), ‖fourierSum f α‖ ∂circleHaar

theorem integrable_norm_fourierSum (f : ℤ →₀ ℂ) :
    Integrable (fun α : AddCircle (1 : ℝ) => ‖fourierSum f α‖) circleHaar :=
  (fourierSum f).continuous.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fourierL1_nonneg (f : ℤ →₀ ℂ) : 0 ≤ fourierL1 f :=
  integral_nonneg fun _ => norm_nonneg _

theorem sum_eq_integral_fourier_test (q : Finset ℤ) (f : ℤ →₀ ℂ) :
    (∑ n ∈ q, f n) = ∫ α : AddCircle (1 : ℝ),
      conj (fourierSum (indicatorFinsupp q) α) * fourierSum f α ∂circleHaar := by
  rw [integral_conj_fourierSum_mul, Finsupp.sum, support_indicatorFinsupp]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hn]

theorem norm_sum_le_fourier_norm_mul_L1 (q : Finset ℤ) (f : ℤ →₀ ℂ) :
    ‖∑ n ∈ q, f n‖ ≤ ‖fourierSum f‖ * fourierL1 (indicatorFinsupp q) := by
  rw [sum_eq_integral_fourier_test]
  calc
    ‖∫ α : AddCircle (1 : ℝ),
        conj (fourierSum (indicatorFinsupp q) α) * fourierSum f α ∂circleHaar‖ ≤
        ∫ α : AddCircle (1 : ℝ),
          ‖fourierSum f‖ * ‖fourierSum (indicatorFinsupp q) α‖ ∂circleHaar := by
      apply norm_integral_le_of_norm_le
        ((integrable_norm_fourierSum _).const_mul ‖fourierSum f‖)
      apply Filter.Eventually.of_forall
      intro α
      simp only [norm_mul, RCLike.norm_conj]
      exact (mul_le_mul_of_nonneg_left ((fourierSum f).norm_coe_le_norm α)
        (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem sum_indicatorFinsupp (q s : Finset ℤ) :
    (∑ n ∈ q, indicatorFinsupp s n) = ((s ∩ q).card : ℂ) := by
  simp only [indicatorFinsupp_apply]
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem card_inter_discrepancy_le_fourierL1 (s t q : Finset ℤ) (δ : ℝ) :
    |((s ∩ q).card : ℝ) - δ * (t ∩ q).card| ≤
      ‖fourierSum (indicatorFinsupp s - δ • indicatorFinsupp t)‖ *
        fourierL1 (indicatorFinsupp q) := by
  have h := norm_sum_le_fourier_norm_mul_L1 q (indicatorFinsupp s - δ • indicatorFinsupp t)
  have hsum : (∑ n ∈ q, (indicatorFinsupp s - δ • indicatorFinsupp t) n) =
      ((((s ∩ q).card : ℝ) - δ * (t ∩ q).card : ℝ) : ℂ) := by
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, Complex.real_smul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicatorFinsupp]
    push_cast
    rfl
  rw [hsum, Complex.norm_real] at h
  exact h

/-- The set of the first `L` terms of an integer arithmetic progression. -/
def arithmeticProgression (a q : ℤ) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image fun j : ℕ => a + q * (j : ℤ)

theorem progression_index_injective (a q : ℤ) (hq : q ≠ 0) :
    Function.Injective (fun j : ℕ => a + q * (j : ℤ)) := by
  intro i j h
  have hij : (i : ℤ) = j := mul_left_cancel₀ hq (add_left_cancel h)
  exact_mod_cast hij

theorem card_arithmeticProgression (a q : ℤ) (L : ℕ) (hq : q ≠ 0) :
    (arithmeticProgression a q L).card = L := by
  rw [arithmeticProgression, Finset.card_image_of_injective _ (progression_index_injective a q hq)]
  exact Finset.card_range _

theorem fourier_mul_nat (q : ℤ) (j : ℕ) (α : AddCircle (1 : ℝ)) :
    fourier (q * (j : ℤ)) α = fourier q α ^ j := by
  induction j with
  | zero => simp only [Nat.cast_zero, mul_zero, fourier_zero, pow_zero]
  | succ j ih =>
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, fourier_add, ih, pow_succ]

theorem fourierSum_arithmeticProgression (a q : ℤ) (L : ℕ) (hq : q ≠ 0)
    (α : AddCircle (1 : ℝ)) :
    fourierSum (indicatorFinsupp (arithmeticProgression a q L)) α =
      fourier a α * ∑ j ∈ Finset.range L, fourier q α ^ j := by
  rw [fourierSum_indicatorFinsupp_apply, arithmeticProgression,
    Finset.sum_image (progression_index_injective a q hq).injOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_add, fourier_mul_nat]

theorem norm_fourierSum_arithmeticProgression_le_length (a q : ℤ) (L : ℕ)
    (hq : q ≠ 0) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (indicatorFinsupp (arithmeticProgression a q L)) α‖ ≤ (L : ℝ) := by
  calc
    _ ≤ ‖fourierSum (indicatorFinsupp (arithmeticProgression a q L))‖ :=
      (fourierSum _).norm_coe_le_norm α
    _ = (L : ℝ) := by rw [norm_fourierSum_indicatorFinsupp, card_arithmeticProgression a q L hq]

theorem norm_fourierSum_progression_mul_denominator_le (a q : ℤ) (L : ℕ)
    (hq : q ≠ 0) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (indicatorFinsupp (arithmeticProgression a q L)) α‖ *
      ‖fourier q α - 1‖ ≤ 2 := by
  rw [fourierSum_arithmeticProgression a q L hq, norm_mul, norm_fourier_apply, one_mul,
    ← norm_mul, geom_sum_mul]
  calc
    ‖fourier q α ^ L - 1‖ ≤ ‖fourier q α ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_fourier_apply, one_pow, norm_one]; norm_num

theorem norm_fourier_one_sub_one (t : ℝ) :
    ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hexp : fourier 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hre : (fourier 1 (t : AddCircle (1 : ℝ))).re = Real.cos (2 * (Real.pi * t)) := by
    rw [hexp]
    exact (Complex.exp_ofReal_mul_I_re (2 * Real.pi * t)).trans (by rw [mul_assoc])
  have hsq : ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ ^ 2 =
      4 * Real.sin (Real.pi * t) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      norm_fourier_apply, one_pow, Complex.normSq_one]
    simp only [map_one, mul_one]
    rw [hre, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  have ha := abs_nonneg (Real.sin (Real.pi * t))
  have hn := norm_nonneg (fourier 1 (t : AddCircle (1 : ℝ)) - 1)
  nlinarith [sq_abs (Real.sin (Real.pi * t))]

theorem four_mul_abs_le_norm_fourier_one_sub_one (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ := by
  rw [norm_fourier_one_sub_one]
  have harg : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  have heq : 2 / Real.pi * |Real.pi * t| = 2 * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [heq] at hs
  linarith

theorem norm_fourierSum_initialProgression_le_inv (L : ℕ) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ‖fourierSum (indicatorFinsupp (arithmeticProgression 0 1 L))
      (t : AddCircle (1 : ℝ))‖ ≤ (2 * t)⁻¹ := by
  have hd := four_mul_abs_le_norm_fourier_one_sub_one t (by rwa [abs_of_pos ht])
  rw [abs_of_pos ht] at hd
  have hg := norm_fourierSum_progression_mul_denominator_le 0 1 L (by norm_num)
    (t : AddCircle (1 : ℝ))
  have hb := (mul_le_mul_of_nonneg_left hd
    (norm_nonneg (fourierSum (indicatorFinsupp (arithmeticProgression 0 1 L))
      (t : AddCircle (1 : ℝ))))).trans hg
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  nlinarith

end Sidon
