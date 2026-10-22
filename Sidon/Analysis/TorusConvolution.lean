import Sidon.Analysis.TorusFourier
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Convolution and autocorrelation on the finite torus -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

variable {d : ℕ}

local instance : circleHaar.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular circleHaar

local instance : (torusHaar d).IsNegInvariant := by
  letI : ∀ _ : Fin d, circleHaar.IsNegInvariant := fun _ => inferInstance
  exact Measure.pi.isNegInvariant (fun _ : Fin d => circleHaar)

private theorem torus_integrable {𝕜 : Type*} [RCLike 𝕜]
    {f : (Fin d → AddCircle (1 : ℝ)) → 𝕜} (hf : Continuous f) :
    Integrable f (torusHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Convolution with probability Haar measure. -/
def torusConvolution {𝕜 : Type*} [RCLike 𝕜]
    (f g : C(Fin d → AddCircle (1 : ℝ), 𝕜)) :
    C(Fin d → AddCircle (1 : ℝ), 𝕜) where
  toFun x := ∫ y, f (x - y) * g y ∂torusHaar d
  continuous_toFun := by
    apply continuous_of_dominated (bound := fun _ => ‖f‖ * ‖g‖)
    · intro x
      exact ((f.continuous.comp (continuous_const.sub continuous_id)).mul g.continuous).aestronglyMeasurable
    · intro x
      exact ae_of_all _ fun y => by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    · exact integrable_const _
    · exact ae_of_all _ fun y =>
        (f.continuous.comp (continuous_id.sub continuous_const)).mul continuous_const

@[simp] theorem torusConvolution_apply {𝕜 : Type*} [RCLike 𝕜]
    (f g : C(Fin d → AddCircle (1 : ℝ), 𝕜)) (x : Fin d → AddCircle (1 : ℝ)) :
    torusConvolution f g x = ∫ y, f (x - y) * g y ∂torusHaar d := rfl

theorem torusCharacter_add_argument (n : Fin d → ℤ)
    (x y : Fin d → AddCircle (1 : ℝ)) :
    torusCharacter n (x + y) = torusCharacter n x * torusCharacter n y := by
  simp only [torusCharacter_apply, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusCharacter_neg_argument (n : Fin d → ℤ) (x : Fin d → AddCircle (1 : ℝ)) :
    torusCharacter n (-x) = conj (torusCharacter n x) := by
  rw [← torusCharacter_neg]
  simp only [torusCharacter_apply, Pi.neg_apply, fourier_apply, smul_neg, neg_smul]

theorem torusFourierCoeff_convolution (f g : C(Fin d → AddCircle (1 : ℝ), ℂ))
    (n : Fin d → ℤ) :
    torusFourierCoeff (torusConvolution f g) n =
      torusFourierCoeff f n * torusFourierCoeff g n := by
  unfold torusFourierCoeff
  conv_lhs => simp only [torusConvolution_apply, ← integral_mul_left]
  rw [integral_integral_swap]
  · calc
      (∫ y, ∫ x, torusCharacter (-n) x * (f (x - y) * g y) ∂torusHaar d ∂torusHaar d) =
          ∫ y, (∫ x, torusCharacter (-n) x * f x ∂torusHaar d) *
            (torusCharacter (-n) y * g y) ∂torusHaar d := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [← integral_add_right_eq_self (fun x =>
          torusCharacter (-n) x * (f (x - y) * g y)) y]
        simp only [add_sub_cancel_right, torusCharacter_add_argument]
        rw [← integral_mul_right]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = _ := integral_mul_left _ _
  · exact (((torusCharacter (-n)).continuous.comp continuous_fst).mul
      ((f.continuous.comp (continuous_fst.sub continuous_snd)).mul
        (g.continuous.comp continuous_snd))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

def torusAdjoint (f : C(Fin d → AddCircle (1 : ℝ), ℂ)) :
    C(Fin d → AddCircle (1 : ℝ), ℂ) where
  toFun x := conj (f (-x))
  continuous_toFun := Complex.continuous_conj.comp (f.continuous.comp continuous_neg)

theorem torusFourierCoeff_adjoint (f : C(Fin d → AddCircle (1 : ℝ), ℂ))
    (n : Fin d → ℤ) :
    torusFourierCoeff (torusAdjoint f) n = conj (torusFourierCoeff f n) := by
  unfold torusFourierCoeff
  rw [← integral_neg_eq_self (fun x => torusCharacter (-n) x * torusAdjoint f x) (torusHaar d)]
  simp only [torusAdjoint, ContinuousMap.coe_mk, neg_neg, torusCharacter_neg_argument,
    ← map_mul]
  exact integral_conj

theorem norm_torusFourierCoeff_le (f : C(Fin d → AddCircle (1 : ℝ), ℂ))
    (n : Fin d → ℤ) : ‖torusFourierCoeff f n‖ ≤ ‖f‖ := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ x, ‖torusCharacter (-n) x * f x‖ ∂torusHaar d) ≤
        ∫ _x : Fin d → AddCircle (1 : ℝ), ‖f‖ ∂torusHaar d := by
      apply integral_mono (torus_integrable (by fun_prop)) (integrable_const _)
      intro x
      change ‖torusCharacter (-n) x * f x‖ ≤ ‖f‖
      rw [norm_mul, norm_torusCharacter_apply, one_mul]
      exact f.norm_coe_le_norm x
    _ = _ := by simp

/-- The autocorrelation has nonnegative, summable Fourier coefficients. -/
theorem torusFourierCoeff_autocorrelation (v : C(Fin d → AddCircle (1 : ℝ), ℂ))
    (n : Fin d → ℤ) :
    torusFourierCoeff (torusConvolution v (torusAdjoint v)) n =
      (‖torusFourierCoeff v n‖ ^ 2 : ℝ) := by
  rw [torusFourierCoeff_convolution, torusFourierCoeff_adjoint, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem hasSum_norm_torusFourierCoeff_autocorrelation
    (v : C(Fin d → AddCircle (1 : ℝ), ℂ)) :
    HasSum (fun n => ‖torusFourierCoeff (torusConvolution v (torusAdjoint v)) n‖)
      (∫ x, ‖v x‖ ^ 2 ∂torusHaar d) := by
  have h := hasSum_sq_torusFourierCoeff (ContinuousMap.toLp (E := ℂ) 2 (torusHaar d) ℂ v)
  simp only [torusFourierCoeff_toLp] at h
  have hi : (∫ x, ‖ContinuousMap.toLp (E := ℂ) 2 (torusHaar d) ℂ v x‖ ^ 2 ∂torusHaar d) =
      ∫ x, ‖v x‖ ^ 2 ∂torusHaar d := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (torusHaar d) v] with x hx
    rw [hx]
  rw [hi] at h
  simpa only [torusFourierCoeff_autocorrelation, Complex.norm_real, Real.norm_eq_abs,
    abs_sq] using h

/-- A real continuous function regarded as complex-valued. -/
def torusComplexify (f : C(Fin d → AddCircle (1 : ℝ), ℝ)) :
    C(Fin d → AddCircle (1 : ℝ), ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp] theorem torusComplexify_apply (f : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (x : Fin d → AddCircle (1 : ℝ)) : torusComplexify f x = (f x : ℂ) := rfl

theorem torusComplexify_convolution (f g : C(Fin d → AddCircle (1 : ℝ), ℝ)) :
    torusComplexify (torusConvolution f g) =
      torusConvolution (torusComplexify f) (torusComplexify g) := by
  ext x
  simp only [torusComplexify_apply, torusConvolution_apply]
  calc
    ((∫ y, f (x - y) * g y ∂torusHaar d : ℝ) : ℂ) =
        ∫ y, ((f (x - y) * g y : ℝ) : ℂ) ∂torusHaar d :=
      (integral_ofReal (𝕜 := ℂ) (μ := torusHaar d) (f := fun y => f (x - y) * g y)).symm
    _ = _ := by simp only [Complex.ofReal_mul]

def torusReflection {𝕜 : Type*} [RCLike 𝕜]
    (f : C(Fin d → AddCircle (1 : ℝ), 𝕜)) :
    C(Fin d → AddCircle (1 : ℝ), 𝕜) where
  toFun x := f (-x)
  continuous_toFun := f.continuous.comp continuous_neg

@[simp] theorem torusReflection_apply {𝕜 : Type*} [RCLike 𝕜]
    (f : C(Fin d → AddCircle (1 : ℝ), 𝕜)) (x : Fin d → AddCircle (1 : ℝ)) :
    torusReflection f x = f (-x) := rfl

theorem torusComplexify_reflection (f : C(Fin d → AddCircle (1 : ℝ), ℝ)) :
    torusComplexify (torusReflection f) = torusAdjoint (torusComplexify f) := by
  ext x
  exact (Complex.conj_ofReal (f (-x))).symm

theorem integral_torusConvolution {𝕜 : Type*} [RCLike 𝕜]
    (f g : C(Fin d → AddCircle (1 : ℝ), 𝕜)) :
    (∫ x, torusConvolution f g x ∂torusHaar d) =
      (∫ x, f x ∂torusHaar d) * ∫ x, g x ∂torusHaar d := by
  simp only [torusConvolution_apply]
  rw [integral_integral_swap]
  · simp_rw [integral_mul_right, integral_sub_right_eq_self]
    exact integral_mul_left _ _
  · exact ((f.continuous.comp (continuous_fst.sub continuous_snd)).mul
      (g.continuous.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem integral_torusReflection {𝕜 : Type*} [RCLike 𝕜]
    (f : C(Fin d → AddCircle (1 : ℝ), 𝕜)) :
    (∫ x, torusReflection f x ∂torusHaar d) = ∫ x, f x ∂torusHaar d :=
  integral_neg_eq_self _ _

theorem torusConvolution_nonneg (f g : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : Fin d → AddCircle (1 : ℝ)) :
    0 ≤ torusConvolution f g x := integral_nonneg fun _y => mul_nonneg (hf _) (hg _)

theorem torusConvolution_le_one (f g : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (hf : ∀ x, f x ≤ 1) (hg : ∀ x, 0 ≤ g x)
    (hgi : (∫ x, g x ∂torusHaar d) = 1) (x : Fin d → AddCircle (1 : ℝ)) :
    torusConvolution f g x ≤ 1 := by
  calc
    torusConvolution f g x ≤ ∫ y, g y ∂torusHaar d := by
      apply integral_mono (torus_integrable (by fun_prop)) (torus_integrable g.continuous)
      intro y
      exact mul_le_of_le_one_left (hg _) (hf _)
    _ = 1 := hgi

theorem torusConvolution_eq_zero_of_support (v : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (r : ℝ) (hv : ∀ x, r < ‖x‖ → v x = 0) (x : Fin d → AddCircle (1 : ℝ))
    (hx : 2 * r < ‖x‖) : torusConvolution v (torusReflection v) x = 0 := by
  apply integral_eq_zero_of_ae
  exact ae_of_all _ fun y => by
    change v (x - y) * torusReflection v y = 0
    by_cases hy : r < ‖y‖
    · rw [torusReflection_apply, hv (-y) (by simpa only [norm_neg] using hy), mul_zero]
    · have hxy : r < ‖x - y‖ := by
        have ht := norm_add_le (x - y) y
        rw [sub_add_cancel] at ht
        linarith [not_lt.mp hy]
      rw [hv (x - y) hxy, zero_mul]

end Sidon
