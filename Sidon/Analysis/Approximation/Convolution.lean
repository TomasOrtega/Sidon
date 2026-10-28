module

public import Sidon.Analysis.Approximation.Tensor
public import Sidon.Analysis.Approximation.Polynomial

@[expose] public section

/-! # Fejér smoothing as a finite trigonometric polynomial -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Sidon

variable {d : ℕ}

local instance approximationCircleNegInvariant : circleHaar.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular circleHaar

local instance approximationTorusNegInvariant : (torusHaar d).IsNegInvariant := by
  letI : ∀ _ : Fin d, circleHaar.IsNegInvariant := fun _ => inferInstance
  exact Measure.pi.isNegInvariant (fun _ : Fin d => circleHaar)

private theorem torus_integrable {𝕜 : Type*} [RCLike 𝕜]
    {f : (Fin d → AddCircle (1 : ℝ)) → 𝕜} (hf : Continuous f) :
    Integrable f (torusHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_convolution_character (F : C(Fin d → AddCircle (1 : ℝ), ℂ))
    (n : Fin d → ℤ) (x : Fin d → AddCircle (1 : ℝ)) :
    (∫ y, F (x - y) * torusCharacter n y ∂torusHaar d) =
      torusFourierCoeff F n * torusCharacter n x := by
  rw [← integral_sub_left_eq_self (fun y => F (x - y) * torusCharacter n y)
    (torusHaar d) x]
  simp only [sub_sub_cancel]
  have hchar : ∀ y, torusCharacter n (x - y) =
      torusCharacter n x * torusCharacter (-n) y := by
    intro y
    rw [sub_eq_add_neg, torusCharacter_add_argument, torusCharacter_neg_argument,
      torusCharacter_neg]
  simp_rw [hchar]
  rw [torusFourierCoeff, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ fun _ => by ring

def fejerApproximation (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (M : ℕ) :
    C(Fin d → AddCircle (1 : ℝ), ℝ) := torusConvolution F (tensorFejer d M)

theorem fejerApproximation_nonneg (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (M : ℕ) (hF : ∀ x, 0 ≤ F x) (x : Fin d → AddCircle (1 : ℝ)) :
    0 ≤ fejerApproximation F M x :=
  torusConvolution_nonneg F (tensorFejer d M) hF (tensorFejer_nonneg d M) x

theorem fejerApproximation_le_one (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    {M : ℕ} (hM : 0 < M) (hF : ∀ x, F x ≤ 1) (x : Fin d → AddCircle (1 : ℝ)) :
    fejerApproximation F M x ≤ 1 :=
  torusConvolution_le_one F (tensorFejer d M) hF (tensorFejer_nonneg d M)
    (integral_tensorFejer d hM) x

theorem fejerApproximation_eq_sum (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    {M : ℕ} (hM : 0 < M) (x : Fin d → AddCircle (1 : ℝ)) :
    (fejerApproximation F M x : ℂ) =
      ∑ n ∈ fejerFrequencyBox d M,
        ((tensorFejerWeight M n : ℂ) * torusFourierCoeff (torusComplexify F) n) *
          torusCharacter n x := by
  change torusComplexify (torusConvolution F (tensorFejer d M)) x = _
  rw [torusComplexify_convolution, torusConvolution_apply]
  simp only [torusComplexify_apply, tensorFejer_eq_sum hM, Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    calc
      (∫ y, (F (x - y) : ℂ) * ((tensorFejerWeight M n : ℂ) * torusCharacter n y)
          ∂torusHaar d) =
          (tensorFejerWeight M n : ℂ) *
            ∫ y, torusComplexify F (x - y) * torusCharacter n y ∂torusHaar d := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun _ => by simp only [torusComplexify_apply]; ring
      _ = _ := by rw [integral_convolution_character]; ring
  · intro n hn
    exact torus_integrable (by fun_prop)

def fejerApproxCoefficients (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (M : ℕ) :
    (Fin d → ℤ) →₀ ℂ :=
  Finsupp.onFinset (fejerFrequencyBox d M)
    (fun n => if n ∈ fejerFrequencyBox d M then
      (tensorFejerWeight M n : ℂ) * torusFourierCoeff (torusComplexify F) n else 0)
    (by intro n hn; by_contra h; exact hn (if_neg h))

theorem support_fejerApproxCoefficients_subset
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (M : ℕ) :
    (fejerApproxCoefficients F M).support ⊆ fejerFrequencyBox d M :=
  Finsupp.support_onFinset_subset

theorem hasTorusBandwidth_fejerApproxCoefficients
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (M : ℕ) :
    HasTorusBandwidth (fejerApproxCoefficients F M) M := by
  intro n hn i
  exact (fejerFrequencyBox_abs_lt (support_fejerApproxCoefficients_subset F M hn) i).le

theorem torusPolynomial_fejerApproxCoefficients
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) {M : ℕ} (hM : 0 < M) :
    torusPolynomial (fejerApproxCoefficients F M) = torusComplexify (fejerApproximation F M) := by
  ext x
  rw [torusPolynomial_apply, torusComplexify_apply, fejerApproximation_eq_sum F hM x]
  calc
    _ = ∑ n ∈ fejerFrequencyBox d M, fejerApproxCoefficients F M n * torusCharacter n x := by
      apply Finset.sum_subset (support_fejerApproxCoefficients_subset F M)
      intro n hn hns
      rw [Finsupp.notMem_support_iff.mp hns, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [fejerApproxCoefficients, Finsupp.onFinset_apply, if_pos hn]

theorem norm_fejerApproxCoefficients_le_one (F : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (M : ℕ) (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) (n : Fin d → ℤ) :
    ‖fejerApproxCoefficients F M n‖ ≤ 1 := by
  have hFnorm : ‖torusComplexify F‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    simpa only [torusComplexify_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hF x).1] using (hF x).2
  simp only [fejerApproxCoefficients, Finsupp.onFinset_apply]
  split_ifs with hn
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tensorFejerWeight_nonneg M n)]
    exact (mul_le_mul (tensorFejerWeight_le_one M n)
      ((norm_torusFourierCoeff_le _ n).trans hFnorm) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
  · norm_num

end Sidon
