import Sidon.Analysis.TorusConvolution
import Sidon.Analysis.CircleBump
import Sidon.Equidistribution.TorusTesting

/-! # Compactly supported smoothing with absolutely convergent character series -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Sidon

variable {d : ℕ}

private theorem torus_real_integrable
    {f : (Fin d → AddCircle (1 : ℝ)) → ℝ} (hf : Continuous f) :
    Integrable f (torusHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_torusConvolution_sub_le (F g : C(Fin d → AddCircle (1 : ℝ), ℝ))
    (K : ℝ≥0) (hF : LipschitzWith K F) (η : ℝ) (_hη : 0 ≤ η)
    (hg : ∀ y, 0 ≤ g y) (hgi : (∫ y, g y ∂torusHaar d) = 1)
    (hgs : ∀ y, η < ‖y‖ → g y = 0) (x : Fin d → AddCircle (1 : ℝ)) :
    ‖torusConvolution F g x - F x‖ ≤ K * η := by
  have heq : torusConvolution F g x - F x =
      ∫ y, (F (x - y) - F x) * g y ∂torusHaar d := by
    simp_rw [sub_mul]
    rw [integral_sub (torus_real_integrable (by fun_prop))
      (torus_real_integrable (by fun_prop)), integral_mul_left, hgi, mul_one]
    rfl
  rw [heq]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ y, ‖(F (x - y) - F x) * g y‖ ∂torusHaar d) ≤
        ∫ y, (K : ℝ) * η * g y ∂torusHaar d := by
      apply integral_mono (torus_real_integrable (by fun_prop)) (torus_real_integrable (by fun_prop))
      intro y
      change ‖(F (x - y) - F x) * g y‖ ≤ (K : ℝ) * η * g y
      by_cases hy : η < ‖y‖
      · rw [hgs y hy, mul_zero, norm_zero, mul_zero]
      · rw [norm_mul, Real.norm_eq_abs (g y), abs_of_nonneg (hg y)]
        apply mul_le_mul_of_nonneg_right _ (hg y)
        have hlip := hF.norm_sub_le (x - y) x
        rw [sub_sub_cancel_left, norm_neg] at hlip
        exact hlip.trans (mul_le_mul_of_nonneg_left (not_lt.mp hy) K.coe_nonneg)
    _ = _ := by rw [integral_mul_left, hgi, mul_one]

/-- A compactly supported probability bump yields a quantitative Fourier smoothing. -/
theorem exists_torus_smoothing_of_bump
    (F v : C(Fin d → AddCircle (1 : ℝ), ℝ)) (K : ℝ≥0) (hF : LipschitzWith K F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (η B : ℝ) (hη : 0 ≤ η) (hv0 : ∀ x, 0 ≤ v x)
    (hvi : (∫ x, v x ∂torusHaar d) = 1)
    (hvs : ∀ x, η / 2 < ‖x‖ → v x = 0)
    (hvB : (∫ x, ‖v x‖ ^ 2 ∂torusHaar d) ≤ B) :
    ∃ A : C(Fin d → AddCircle (1 : ℝ), ℝ),
      (∀ x, 0 ≤ A x) ∧ (∀ x, A x ≤ 1) ∧ (∀ x, ‖A x - F x‖ ≤ K * η) ∧
      ∃ a : (Fin d → ℤ) → ℂ, Summable (fun n => ‖a n‖) ∧
        (∑' n, ‖a n‖) ≤ B ∧
        ∀ x, HasSum (fun n => a n * torusCharacter n x) (A x : ℂ) := by
  let g := torusConvolution v (torusReflection v)
  have hg0 : ∀ x, 0 ≤ g x :=
    torusConvolution_nonneg v (torusReflection v) hv0 (fun x => hv0 (-x))
  have hgi : (∫ x, g x ∂torusHaar d) = 1 := by
    rw [integral_torusConvolution, integral_torusReflection, hvi, one_mul]
  have hgs : ∀ x, η < ‖x‖ → g x = 0 := by
    intro x hx
    exact torusConvolution_eq_zero_of_support v (η / 2) hvs x (by linarith)
  let A := torusConvolution F g
  refine ⟨A, torusConvolution_nonneg F g hF0 hg0,
    torusConvolution_le_one F g hF1 hg0 hgi,
    norm_torusConvolution_sub_le F g K hF η hη hg0 hgi hgs, ?_⟩
  let a := torusFourierCoeff (torusComplexify A)
  have hmass : HasSum (fun n => ‖torusFourierCoeff (torusComplexify g) n‖)
      (∫ x, ‖v x‖ ^ 2 ∂torusHaar d) := by
    have h := hasSum_norm_torusFourierCoeff_autocorrelation (torusComplexify v)
    rw [← torusComplexify_reflection, ← torusComplexify_convolution] at h
    simpa only [torusComplexify_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hnormF : ‖torusComplexify F‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    rw [torusComplexify_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
    exact hF1 x
  have hbound : ∀ n, ‖a n‖ ≤ ‖torusFourierCoeff (torusComplexify g) n‖ := by
    intro n
    change ‖torusFourierCoeff (torusComplexify (torusConvolution F g)) n‖ ≤ _
    rw [torusComplexify_convolution, torusFourierCoeff_convolution, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((norm_torusFourierCoeff_le _ _).trans hnormF)
  have ha : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmass.summable
  refine ⟨a, ha, (tsum_le_tsum hbound ha hmass.summable).trans (hmass.tsum_eq.le.trans hvB), ?_⟩
  exact hasSum_torusFourier_series_apply_of_summable ha.of_norm

/-- Tensoring a circle bump preserves its support in the maximum metric. -/
def torusTensor (v : C(AddCircle (1 : ℝ), ℝ)) (d : ℕ) :
    C(Fin d → AddCircle (1 : ℝ), ℝ) where
  toFun x := ∏ i, v (x i)
  continuous_toFun := by fun_prop

@[simp] theorem torusTensor_apply (v : C(AddCircle (1 : ℝ), ℝ))
    (x : Fin d → AddCircle (1 : ℝ)) : torusTensor v d x = ∏ i, v (x i) := rfl

theorem torusTensor_nonneg (v : C(AddCircle (1 : ℝ), ℝ)) (hv : ∀ x, 0 ≤ v x)
    (x : Fin d → AddCircle (1 : ℝ)) : 0 ≤ torusTensor v d x :=
  by
    change 0 ≤ ∏ i : Fin d, v (x i)
    exact Finset.prod_nonneg fun i _ => hv (x i)

theorem torusTensor_eq_zero_of_support (v : C(AddCircle (1 : ℝ), ℝ))
    (r : ℝ) (hr : 0 ≤ r) (hv : ∀ x, r < ‖x‖ → v x = 0)
    (x : Fin d → AddCircle (1 : ℝ)) (hx : r < ‖x‖) : torusTensor v d x = 0 := by
  classical
  have hi : ∃ i, r < ‖x i‖ := by
    by_contra! h
    exact (not_lt_of_ge ((pi_norm_le_iff_of_nonneg hr).mpr h)) hx
  obtain ⟨i, hi⟩ := hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hv (x i) hi)

local instance : MeasureSpace (AddCircle (1 : ℝ)) := ⟨circleHaar⟩
local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (IsProbabilityMeasure circleHaar)
local instance : SigmaFinite (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (SigmaFinite circleHaar)

theorem integral_torusTensor (v : C(AddCircle (1 : ℝ), ℝ)) :
    (∫ x, torusTensor v d x ∂torusHaar d) = (∫ x, v x ∂circleHaar) ^ d := by
  change (∫ x : Fin d → AddCircle (1 : ℝ), ∏ i, v (x i)) = _
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow (𝕜 := ℝ) (E := AddCircle (1 : ℝ)) (Fin d) (fun x => v x)

theorem integral_sq_norm_torusTensor (v : C(AddCircle (1 : ℝ), ℝ)) :
    (∫ x, ‖torusTensor v d x‖ ^ 2 ∂torusHaar d) =
      (∫ x, ‖v x‖ ^ 2 ∂circleHaar) ^ d := by
  simp only [torusTensor_apply, norm_prod, ← Finset.prod_pow]
  change (∫ x : Fin d → AddCircle (1 : ℝ), ∏ i, ‖v (x i)‖ ^ 2) = _
  simpa only [Fintype.card_fin] using
    integral_fintype_prod_eq_pow (𝕜 := ℝ) (E := AddCircle (1 : ℝ)) (Fin d) (fun x : AddCircle (1 : ℝ) => ‖v x‖ ^ 2)

/-- Dimension-uniform compact smoothing; the coefficient series may have infinite support. -/
theorem exists_torus_smoothing
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (K : ℝ≥0) (hF : LipschitzWith K F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    ∃ A : C(Fin d → AddCircle (1 : ℝ), ℝ),
      (∀ x, 0 ≤ A x) ∧ (∀ x, A x ≤ 1) ∧ (∀ x, ‖A x - F x‖ ≤ K * η) ∧
      ∃ a : (Fin d → ℤ) → ℂ, Summable (fun n => ‖a n‖) ∧
        (∑' n, ‖a n‖) ≤ (10 / η) ^ d ∧
        ∀ x, HasSum (fun n => a n * torusCharacter n x) (A x : ℂ) := by
  obtain ⟨v, hv0, hvi, hvs, hvB⟩ := exists_circleBump hη hη₁
  apply exists_torus_smoothing_of_bump F (torusTensor v d) K hF hF0 hF1 η
    ((10 / η) ^ d) hη.le (torusTensor_nonneg v hv0)
  · rw [integral_torusTensor, hvi, one_pow]
  · exact torusTensor_eq_zero_of_support v (η / 2) (by positivity) hvs
  · rw [integral_sq_norm_torusTensor]
    gcongr

theorem norm_torusTest_le_compact_smoothing (f : ℤ →₀ ℂ)
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (K : ℝ≥0) (hF : LipschitzWith K F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (α : Fin d → AddCircle (1 : ℝ)) (D η : ℝ)
    (hD : ∀ β, ‖fourierSum f β‖ ≤ D) (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    ‖torusTest f (torusComplexify F) α‖ ≤
      (K : ℝ) * η * f.sum (fun _ c => ‖c‖) + D * (10 / η) ^ d := by
  obtain ⟨A, _hA0, _hA1, hAF, a, ha, hmass, hseries⟩ :=
    exists_torus_smoothing F K hF hF0 hF1 η hη hη₁
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have happrox := norm_torusTest_sub_le f (torusComplexify F) (torusComplexify A) α
    ((K : ℝ) * η) (fun x => by
      rw [torusComplexify_apply, torusComplexify_apply, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, ← Real.norm_eq_abs, norm_sub_rev]
      exact hAF x)
  have htest := (norm_torusTest_le_fourier_bound f (torusComplexify A) a ha hseries α D hD).trans
    (mul_le_mul_of_nonneg_left hmass hD0)
  calc
    ‖torusTest f (torusComplexify F) α‖ ≤
        ‖torusTest f (torusComplexify F) α - torusTest f (torusComplexify A) α‖ +
          ‖torusTest f (torusComplexify A) α‖ := by
            simpa only [sub_add_cancel] using norm_add_le
              (torusTest f (torusComplexify F) α - torusTest f (torusComplexify A) α)
              (torusTest f (torusComplexify A) α)
    _ ≤ _ := add_le_add happrox htest

end Sidon
