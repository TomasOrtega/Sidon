import Sidon.Analysis.Approximation.Fejer

/-! # Finite-bandwidth tensor Fejér kernels -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Sidon

local instance tensorCircleMeasureSpace : MeasureSpace (AddCircle (1 : ℝ)) := ⟨circleHaar⟩
local instance tensorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (Measure.IsAddHaarMeasure circleHaar)
local instance tensorCircleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (IsProbabilityMeasure circleHaar)

def tensorFejer (d M : ℕ) : C(Fin d → AddCircle (1 : ℝ), ℝ) where
  toFun x := ∏ i, circleFejer M (x i)
  continuous_toFun := by fun_prop

def tensorFejerOmit {d : ℕ} (M : ℕ) (i : Fin d) :
    C(Fin d → AddCircle (1 : ℝ), ℝ) where
  toFun x := ∏ j : Fin d, if j = i then 1 else circleFejer M (x j)
  continuous_toFun := by
    apply continuous_finset_prod
    intro j hj
    split_ifs <;> fun_prop

theorem tensorFejer_nonneg (d M : ℕ) (x : Fin d → AddCircle (1 : ℝ)) :
    0 ≤ tensorFejer d M x := by
  change 0 ≤ ∏ i : Fin d, circleFejer M (x i)
  exact Finset.prod_nonneg fun _ _ => circleFejer_nonneg _ _

theorem tensorFejerOmit_nonneg {d : ℕ} (M : ℕ) (i : Fin d)
    (x : Fin d → AddCircle (1 : ℝ)) : 0 ≤ tensorFejerOmit M i x := by
  change 0 ≤ ∏ j : Fin d, if j = i then 1 else circleFejer M (x j)
  apply Finset.prod_nonneg
  intro j hj
  change 0 ≤ if j = i then 1 else circleFejer M (x j)
  split_ifs
  · norm_num
  · exact circleFejer_nonneg _ _

theorem integral_tensorFejer (d : ℕ) {M : ℕ} (hM : 0 < M) :
    (∫ x, tensorFejer d M x ∂torusHaar d) = 1 := by
  change (∫ x : Fin d → AddCircle (1 : ℝ), ∏ i, circleFejer M (x i)
    ∂Measure.pi (fun _ => circleHaar)) = 1
  rw [integral_fintype_prod_eq_prod
    (E := fun _ => AddCircle (1 : ℝ)) (μ := fun _ => circleHaar) (fun _ => circleFejer M)]
  change (∏ _i : Fin d, ∫ x, circleFejer M x ∂circleHaar) = 1
  simp only [integral_circleFejer hM, Finset.prod_const_one]

theorem integral_tensorFejerOmit {d : ℕ} {M : ℕ} (hM : 0 < M) (i : Fin d) :
    (∫ x, tensorFejerOmit M i x ∂torusHaar d) = 1 := by
  change (∫ x : Fin d → AddCircle (1 : ℝ),
    ∏ j : Fin d, (if j = i then (1 : ℝ) else circleFejer M (x j))
      ∂Measure.pi (fun _ => circleHaar)) = 1
  have hpoint : (fun x : Fin d → AddCircle (1 : ℝ) =>
      ∏ j : Fin d, if j = i then (1 : ℝ) else circleFejer M (x j)) =
      (fun x => ∏ j : Fin d, (fun y => if j = i then (1 : ℝ) else circleFejer M y) (x j)) := rfl
  rw [hpoint, integral_fintype_prod_eq_prod
    (E := fun _ => AddCircle (1 : ℝ))
    (μ := fun _ => circleHaar)
    (fun j y => if j = i then (1 : ℝ) else circleFejer M y)]
  apply Finset.prod_eq_one
  intro j hj
  by_cases hji : j = i
  · simp only [hji, if_pos]
    change (∫ _x : AddCircle (1 : ℝ), (1 : ℝ) ∂circleHaar) = 1
    simp
  · simpa only [hji, if_false] using integral_circleFejer hM

theorem tensorFejer_eq_mul_omit {d : ℕ} (M : ℕ) (i : Fin d)
    (x : Fin d → AddCircle (1 : ℝ)) :
    tensorFejer d M x = circleFejer M (x i) * tensorFejerOmit M i x := by
  change (∏ j : Fin d, circleFejer M (x j)) =
    circleFejer M (x i) * ∏ j : Fin d, if j = i then 1 else circleFejer M (x j)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [if_pos, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact (if_neg (Finset.mem_erase.mp hj).1).symm

theorem tensorFejer_le_sum_omit_of_norm_gt {d M : ℕ} {η : ℝ} (hη : 0 < η)
    (x : Fin d → AddCircle (1 : ℝ)) (hx : η < ‖x‖) :
    tensorFejer d M x ≤ ∑ i : Fin d, (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M i x := by
  have hex : ∃ i : Fin d, η < ‖x i‖ := by
    by_contra h
    push_neg at h
    exact not_le.mpr hx ((pi_norm_le_iff_of_nonneg hη.le).mpr h)
  obtain ⟨i, hi⟩ := hex
  calc
    tensorFejer d M x = circleFejer M (x i) * tensorFejerOmit M i x :=
      tensorFejer_eq_mul_omit M i x
    _ ≤ (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M i x :=
      mul_le_mul_of_nonneg_right (circleFejer_le_of_norm_gt hη (x i) hi)
        (tensorFejerOmit_nonneg M i x)
    _ ≤ ∑ j : Fin d, (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M j x := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M j x)
      · intro j hj
        exact mul_nonneg (by positivity) (tensorFejerOmit_nonneg M j x)
      · exact Finset.mem_univ i

theorem integral_tensorFejer_tail_le {d M : ℕ} (hM : 0 < M) {η : ℝ} (hη : 0 < η) :
    (∫ x in {x : Fin d → AddCircle (1 : ℝ) | η < ‖x‖}, tensorFejer d M x ∂torusHaar d) ≤
      (d : ℝ) / ((M : ℝ) * η ^ 2) := by
  let g := fun x : Fin d → AddCircle (1 : ℝ) =>
    ∑ i : Fin d, (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M i x
  have hg : Integrable g (torusHaar d) :=
    (by fun_prop : Continuous g).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf : Integrable (tensorFejer d M) (torusHaar d) :=
    (tensorFejer d M).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x in {x : Fin d → AddCircle (1 : ℝ) | η < ‖x‖}, g x ∂torusHaar d := by
      apply setIntegral_mono_on hf.integrableOn hg.integrableOn
        (measurableSet_lt measurable_const continuous_norm.measurable)
      intro x hx
      exact tensorFejer_le_sum_omit_of_norm_gt hη x hx
    _ ≤ ∫ x, g x ∂torusHaar d := by
      apply setIntegral_le_integral hg
      exact ae_of_all _ fun x => Finset.sum_nonneg fun i _ =>
        mul_nonneg (by positivity) (tensorFejerOmit_nonneg M i x)
    _ = _ := by
      dsimp [g]
      rw [integral_finset_sum _ (fun i _ =>
        (show Continuous (fun x => (1 / ((M : ℝ) * η ^ 2)) * tensorFejerOmit M i x)
          from continuous_const.mul (tensorFejerOmit M i).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
      simp only [integral_const_mul, integral_tensorFejerOmit hM, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

def fejerFrequencyBox (d M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => (fejerWeight M).support)

def tensorFejerWeight {d : ℕ} (M : ℕ) (n : Fin d → ℤ) : ℝ :=
  ∏ i, circleFejerSpectrum M (n i)

theorem tensorFejerWeight_nonneg {d : ℕ} (M : ℕ) (n : Fin d → ℤ) :
    0 ≤ tensorFejerWeight M n :=
  Finset.prod_nonneg fun _ _ => circleFejerSpectrum_nonneg _ _

theorem tensorFejerWeight_le_one {d : ℕ} (M : ℕ) (n : Fin d → ℤ) :
    tensorFejerWeight M n ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact circleFejerSpectrum_nonneg _ _
  · intro i hi
    exact circleFejerSpectrum_le_one _ _

theorem fejerFrequencyBox_abs_lt {d M : ℕ} {n : Fin d → ℤ}
    (hn : n ∈ fejerFrequencyBox d M) (i : Fin d) : |n i| < (M : ℤ) := by
  apply abs_lt_of_mem_support_fejerWeight M
  exact (Fintype.mem_piFinset.mp hn) i

theorem tensorFejer_eq_sum {d M : ℕ} (hM : 0 < M)
    (x : Fin d → AddCircle (1 : ℝ)) :
    (tensorFejer d M x : ℂ) =
      ∑ n ∈ fejerFrequencyBox d M, (tensorFejerWeight M n : ℂ) * torusCharacter n x := by
  change ((∏ i : Fin d, circleFejer M (x i) : ℝ) : ℂ) = _
  rw [Complex.ofReal_prod]
  simp_rw [circleFejer_eq_weightSum hM]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib]
  simp only [tensorFejerWeight, Complex.ofReal_prod, torusCharacter_apply]

end Sidon
