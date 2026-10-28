module

public import Sidon.Analysis.FejerClosedForm
public import Sidon.Analysis.TorusConvolution
public import Sidon.Equidistribution.Progressions

@[expose] public section

/-! # Continuous Fejér kernels on the unit circle -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Sidon

def circleDirichlet (M : ℕ) : C(AddCircle (1 : ℝ), ℂ) :=
  fourierSum (indicatorFinsupp (arithmeticProgression 0 1 M))

def circleFejer (M : ℕ) : C(AddCircle (1 : ℝ), ℝ) where
  toFun x := ‖circleDirichlet M x‖ ^ 2 / M
  continuous_toFun := by unfold circleDirichlet; fun_prop

@[simp] theorem circleFejer_apply (M : ℕ) (x : AddCircle (1 : ℝ)) :
    circleFejer M x = ‖circleDirichlet M x‖ ^ 2 / M := rfl

theorem circleFejer_nonneg (M : ℕ) (x : AddCircle (1 : ℝ)) :
    0 ≤ circleFejer M x := by rw [circleFejer_apply]; positivity

theorem integral_circleFejer {M : ℕ} (hM : 0 < M) :
    (∫ x, circleFejer M x ∂circleHaar) = 1 := by
  simp only [circleFejer_apply, integral_div]
  rw [circleDirichlet, integral_norm_fourierSum_indicator_sq,
    card_arithmeticProgression 0 1 M (by norm_num)]
  exact div_self (by exact_mod_cast ne_of_gt hM)

theorem four_mul_norm_le_norm_fourier_sub_one (x : AddCircle (1 : ℝ)) :
    4 * ‖x‖ ≤ ‖fourier 1 x - 1‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
      let t := a - (round a : ℤ)
      have hint : (((round a : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
        exact ⟨round a, by simp⟩
      have heq : (t : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
        rw [show t = a - (round a : ℤ) from rfl, AddCircle.coe_sub, hint, sub_zero]
      have hnorm : ‖(a : AddCircle (1 : ℝ))‖ = |t| := UnitAddCircle.norm_eq
      have hhalf : |t| ≤ 1 / 2 := by
        rw [← hnorm]
        simpa using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero
          (x := (a : AddCircle (1 : ℝ)))
      simpa only [heq, ← hnorm] using four_mul_abs_le_norm_fourier_one_sub_one t hhalf

theorem circleFejer_mul_norm_sq_le (M : ℕ) (x : AddCircle (1 : ℝ)) :
    circleFejer M x * ‖x‖ ^ 2 ≤ 1 / (M : ℝ) := by
  have hgeom := norm_fourierSum_progression_mul_denominator_le 0 1 M (by norm_num) x
  have hgap := four_mul_norm_le_norm_fourier_sub_one x
  have hbound : ‖circleDirichlet M x‖ * ‖x‖ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hgap (norm_nonneg (circleDirichlet M x))
    change ‖circleDirichlet M x‖ * ‖fourier 1 x - 1‖ ≤ 2 at hgeom
    nlinarith [norm_nonneg (circleDirichlet M x), norm_nonneg x]
  rw [circleFejer_apply, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  have hs := pow_le_pow_left₀ (mul_nonneg (norm_nonneg (circleDirichlet M x))
    (norm_nonneg x)) hbound 2
  simpa only [mul_pow, one_pow] using hs

theorem circleFejer_le_of_norm_gt {M : ℕ} {η : ℝ} (hη : 0 < η)
    (x : AddCircle (1 : ℝ)) (hx : η < ‖x‖) :
    circleFejer M x ≤ 1 / ((M : ℝ) * η ^ 2) := by
  by_cases hM : M = 0
  · simp [hM, circleFejer_apply]
  · have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    have h := circleFejer_mul_norm_sq_le M x
    have hsmall : circleFejer M x * η ^ 2 ≤ 1 / (M : ℝ) := by
      have hnorm : η ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      exact (mul_le_mul_of_nonneg_left hnorm (circleFejer_nonneg M x)).trans h
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < M * η ^ 2)).mpr
    have h' := (le_div_iff₀ hMp).mp hsmall
    nlinarith

def circleFejerSpectrum (M : ℕ) : ℤ →₀ ℝ := (M : ℝ) • fejerWeight M

theorem circleFejerSpectrum_nonneg (M : ℕ) (n : ℤ) :
    0 ≤ circleFejerSpectrum M n := by
  exact mul_nonneg (Nat.cast_nonneg M) (fejerWeight_nonneg M n)

theorem circleFejerSpectrum_le_one (M : ℕ) (n : ℤ) :
    circleFejerSpectrum M n ≤ 1 := by
  change (M : ℝ) * fejerWeight M n ≤ 1
  rw [fejerWeight_eq_nat_sub]
  by_cases hM : M = 0
  · simp [hM]
  · have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    have hsub : ((M - n.natAbs : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M n.natAbs
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hMp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsub hMp.le]

theorem circleFejerSpectrum_eq_max {M : ℕ} (hM : 0 < M) (n : ℤ) :
    circleFejerSpectrum M n = max (1 - (n.natAbs : ℝ) / M) 0 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  change (M : ℝ) * fejerWeight M n = _
  rw [fejerWeight_eq_nat_sub]
  by_cases hn : n.natAbs ≤ M
  · have hn' : (n.natAbs : ℝ) ≤ M := by exact_mod_cast hn
    rw [Nat.cast_sub hn, max_eq_left (sub_nonneg.mpr ((div_le_one hMp).mpr hn'))]
    field_simp
  · have hn' : (M : ℝ) ≤ n.natAbs := by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hn)
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge hn)), Nat.cast_zero,
      zero_div, mul_zero, max_eq_right (by
        have h : (1 : ℝ) ≤ (n.natAbs : ℝ) / M :=
          (le_div_iff₀ hMp).mpr (by simpa using hn')
        linarith)]

theorem abs_lt_of_mem_circleFejerSpectrum {M : ℕ} {n : ℤ}
    (hn : n ∈ (circleFejerSpectrum M).support) : |n| < (M : ℤ) := by
  apply abs_lt_of_mem_support_fejerWeight M
  contrapose! hn
  simp only [Finsupp.mem_support_iff, not_not] at *
  change (M : ℝ) * fejerWeight M n = 0
  rw [hn, mul_zero]

theorem circleDirichlet_eq_sum (M : ℕ) (x : AddCircle (1 : ℝ)) :
    circleDirichlet M x = ∑ j ∈ Finset.range M, fourier (j : ℤ) x := by
  rw [circleDirichlet, fourierSum_arithmeticProgression 0 1 M (by norm_num)]
  simp only [fourier_zero, one_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [one_mul] using (fourier_mul_nat 1 j x).symm

theorem sum_fourier_differences_eq_norm_sq (M : ℕ) (x : AddCircle (1 : ℝ)) :
    (∑ u ∈ Finset.range M, ∑ v ∈ Finset.range M,
      fourier ((v : ℤ) - u) x) = (‖circleDirichlet M x‖ ^ 2 : ℝ) := by
  calc
    _ = conj (circleDirichlet M x) * circleDirichlet M x := by
      rw [circleDirichlet_eq_sum, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [sub_eq_add_neg, fourier_add, fourier_neg]
      ring
    _ = _ := by rw [Complex.conj_mul', ← Complex.ofReal_pow]

theorem circleFejer_eq_weightSum {M : ℕ} (hM : 0 < M) (x : AddCircle (1 : ℝ)) :
    (circleFejer M x : ℂ) =
      ∑ n ∈ (fejerWeight M).support, (circleFejerSpectrum M n : ℂ) * fourier n x := by
  have h := sum_fejerWeight_smul M (fun n => fourier (T := 1) n x)
  simp only [Complex.real_smul] at h
  have hsum : (fejerWeight M).sum (fun n w => (w : ℂ) * fourier n x) =
      (((M : ℝ) ^ 2)⁻¹ : ℝ) * (‖circleDirichlet M x‖ ^ 2 : ℝ) := by
    rw [h]
    simp only [← Finset.mul_sum]
    rw [sum_fourier_differences_eq_norm_sq]
  calc
    (circleFejer M x : ℂ) = (M : ℂ) *
        ((((M : ℝ) ^ 2)⁻¹ : ℝ) * (‖circleDirichlet M x‖ ^ 2 : ℝ)) := by
      rw [circleFejer_apply]
      push_cast
      have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
      field_simp
    _ = (M : ℂ) * (fejerWeight M).sum (fun n w => (w : ℂ) * fourier n x) := by rw [hsum]
    _ = _ := by
      rw [Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [circleFejerSpectrum, Finsupp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
        Complex.ofReal_natCast]
      ring

end Sidon
