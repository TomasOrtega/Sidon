module

public import Sidon.NumberTheory.MollifierInterpolation
public import Sidon.NumberTheory.MollifierRightHalfPlane

@[expose] public section

/-! # The power-saving exponent in the actual mollifier mean square -/

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem mollifier_interpolation_power_bound {R L B σ₀ σ : ℝ}
    (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ)
    (hσ1 : σ ≤ 1 + 1 / Real.log R) :
    (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^
        (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
      (B * Real.log R ^ 8) ^
        ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) ≤
      L * B * Real.exp (11 / 4) * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 < Real.log R := by linarith
  let θ := (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)
  have hden : 0 < 1 + 1 / Real.log R - 1 / 2 := by
    linarith [one_div_pos.mpr hlog0]
  have hθ : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden).mpr (by linarith)
  have hq : 0 ≤ 1 - θ := by linarith
  have hq1 : 1 - θ ≤ 1 := by linarith
  have hqbound : 1 - θ ≤ 2 * (1 - σ₀ + 1 / Real.log R) := by
    have heq : 1 - θ = (1 + 1 / Real.log R - σ) /
        (1 + 1 / Real.log R - 1 / 2) := by
      dsimp [θ]
      rw [one_sub_div hden.ne']
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ (1 + 1 / Real.log R - σ) / (1 / 2) := by
        apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
        linarith [one_div_pos.mpr hlog0]
      _ ≤ _ := by norm_num; linarith
  have hfactor : 1 ≤ L * Real.log R := by nlinarith
  have hleft : (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^ (1 - θ) ≤
      (L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR0.le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hfactor hq1) (by positivity)
  have hright : (B * Real.log R ^ 8) ^ θ ≤ B * Real.log R ^ 8 := by
    apply Real.rpow_le_self_of_one_le _ hθ1
    have hp : 1 ≤ Real.log R ^ 8 := one_le_pow₀ (by linarith : 1 ≤ Real.log R)
    nlinarith
  have hpower : R ^ (((11 : ℝ) / 8) * (1 - θ)) ≤
      R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4) := by
    calc
      _ ≤ R ^ ((11 / 4 : ℝ) * (1 - σ₀) + (11 / 4 : ℝ) / Real.log R) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hh := mul_le_mul_of_nonneg_left hqbound (by norm_num : (0 : ℝ) ≤ 11 / 8)
        convert hh using 1 <;> ring
      _ = _ := by
        rw [Real.rpow_add hR0]
        congr 1
        rw [Real.rpow_def_of_pos hR0]
        congr 1
        field_simp
  change (_ ^ (1 - θ) * _ ^ θ) ≤ _
  calc
    _ ≤ ((L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ))) *
        (B * Real.log R ^ 8) := mul_le_mul hleft hright (by positivity) (by positivity)
    _ ≤ ((L * Real.log R) * (R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4))) *
        (B * Real.log R ^ 8) := by gcongr
    _ = _ := by ring

theorem ceil_mollifier_parameters {R : ℝ} (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) :
    1 ≤ ⌈R⌉₊ ∧ R ≤ (⌈R⌉₊ : ℝ) ∧ (⌈R⌉₊ : ℝ) ≤ 2 * R ∧
      1 + Real.log (⌈R⌉₊ : ℝ) ≤ 2 * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hRN : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hN1 : (1 : ℝ) ≤ ⌈R⌉₊ := hR.trans hRN
  have hNR : (⌈R⌉₊ : ℝ) ≤ 2 * R := by
    have hh := Nat.ceil_lt_add_one hR0.le
    linarith
  refine ⟨by exact_mod_cast hN1, hRN, hNR, ?_⟩
  have hlogN := Real.log_le_log (by linarith : (0 : ℝ) < ⌈R⌉₊) hNR
  rw [Real.log_mul (by norm_num) hR0.ne'] at hlogN
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

theorem exists_mollifier_optimized_interior_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → 2 ≤ Real.log R →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 → ∀ σ : ℝ, σ₀ ≤ σ →
        σ ≤ 1 + 1 / Real.log R →
      (∫ t in (1 : ℝ)..R,
        ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  obtain ⟨K₀, hK₀, hleft⟩ := exists_verticalL2_gaussianMollifier_left_bound
  let L := max (6 * K₀) 1
  let B := max (8192 * Real.exp 6 * gaussianCumulativeConstant) 1
  have hL : 1 ≤ L := le_max_right _ _
  have hB : 1 ≤ B := le_max_right _ _
  refine ⟨8 * Real.exp 2 * (L * B * Real.exp (11 / 4)), by positivity, ?_⟩
  intro R hR hlog σ₀ hσ₀ hσ₀1 σ hσ hσ1
  obtain ⟨hN, hRN, hNR, hlogN⟩ := ceil_mollifier_parameters hR hlog
  have hR0 : 0 < R := by linarith
  have hN0 : (0 : ℝ) < ⌈R⌉₊ := hR0.trans_le hRN
  have hlog0 : 0 < Real.log R := by linarith
  have hδ : 0 < 1 / Real.log R := one_div_pos.mpr hlog0
  have hδhalf : 1 / Real.log R ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hlog
  have hG0 : 0 ≤ gaussianCumulativeConstant := gaussianCumulativeConstant_pos.le
  have hJl : 0 ≤ verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) := verticalL2_nonneg _ _
  have hJr : 0 ≤ verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) := verticalL2_nonneg _ _
  have hleftR : verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) ≤
      L * Real.log R * R ^ ((11 : ℝ) / 8) := by
    calc
      _ ≤ K₀ * (1 + Real.log (⌈R⌉₊ : ℝ)) * (R + ⌈R⌉₊) * R ^ ((3 : ℝ) / 8) :=
        hleft _ hN R hR
      _ ≤ K₀ * (2 * Real.log R) * (3 * R) * R ^ ((3 : ℝ) / 8) := by gcongr <;> linarith
      _ = (6 * K₀) * Real.log R * R ^ ((11 : ℝ) / 8) := by
        have heq : R * R ^ ((3 : ℝ) / 8) = R ^ ((11 : ℝ) / 8) := by
          conv_lhs => lhs; rw [← Real.rpow_one R]
          rw [← Real.rpow_add hR0]
          norm_num
        calc
          _ = (6 * K₀) * Real.log R * (R * R ^ ((3 : ℝ) / 8)) := by ring
          _ = _ := by rw [heq]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hrightR : verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) ≤
      B * Real.log R ^ 8 := by
    calc
      _ ≤ (4096 * Real.exp 6 * gaussianCumulativeConstant) * (R + ⌈R⌉₊) /
          ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 8) :=
        verticalL2_gaussianMollifier_right_bound hN hR hδ hδhalf
      _ ≤ (4096 * Real.exp 6 * gaussianCumulativeConstant) * (2 * (⌈R⌉₊ : ℝ)) /
          ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 8) := by gcongr <;> first | positivity | linarith
      _ = (8192 * Real.exp 6 * gaussianCumulativeConstant) * Real.log R ^ 8 := by
        field_simp
        ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hθ : 0 ≤ (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) := by
    exact div_nonneg (by linarith) (by linarith [hδ])
  have hq : 0 ≤ 1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) := by
    have hd : 0 < 1 + 1 / Real.log R - 1 / 2 := by linarith [hδ]
    have hh : (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) ≤ 1 :=
      (div_le_one hd).mpr (by linarith)
    linarith
  calc
    _ ≤ 8 * Real.exp 2 *
        (verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) ^
          (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
        verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) ^
          ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2))) :=
      integral_mollifierError_interpolation hR hδ hδhalf ⟨by linarith, hσ1⟩
    _ ≤ 8 * Real.exp 2 *
        ((L * Real.log R * R ^ ((11 : ℝ) / 8)) ^
          (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
        (B * Real.log R ^ 8) ^ ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2))) := by
      gcongr <;> positivity
    _ ≤ 8 * Real.exp 2 *
        (L * B * Real.exp (11 / 4) * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mollifier_interpolation_power_bound hR hlog hL hB hσ₀ hσ₀1 hσ hσ1
    _ = _ := by ring

theorem mollifier_optimized_right_bound {R σ : ℝ} (hR : 1 ≤ R)
    (hlog : 2 ≤ Real.log R) (hσ : 1 + 1 / Real.log R ≤ σ) :
    (∫ t in (1 : ℝ)..R,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤ 1552 * Real.log R ^ 9 := by
  obtain ⟨hN, hRN, _, _⟩ := ceil_mollifier_parameters hR hlog
  have hlog0 : 0 < Real.log R := by linarith
  have hN0 : (0 : ℝ) < ⌈R⌉₊ := (show 0 < R by linarith).trans_le hRN
  have hδ : 0 < 1 / Real.log R := by positivity
  have hδ1 : 1 / Real.log R ≤ 1 := by
    apply (div_le_one hlog0).mpr
    linarith
  have hc := (continuous_mollifierError_vertical ⌈R⌉₊ (σ := σ) (by linarith)).norm.pow 2
  have hi0 : IntervalIntegrable
      (fun t : ℝ => ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) volume 0 1 :=
    hc.intervalIntegrable _ _
  have hi1 : IntervalIntegrable
      (fun t : ℝ => ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) volume 1 R :=
    hc.intervalIntegrable _ _
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hraw := integral_mollifierError_right_halfPlane_le hN hδ hδ1 hσ (by linarith : 0 ≤ R)
  have hdiag : R * (16 / ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 4)) ≤ 16 * Real.log R ^ 4 := by
    calc
      _ = (16 * Real.log R ^ 4) * (R / (⌈R⌉₊ : ℝ)) := by field_simp <;> ring
      _ ≤ (16 * Real.log R ^ 4) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one hN0).mpr hRN
      _ = _ := mul_one _
  have h4 : Real.log R ^ 4 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h8 : Real.log R ^ 8 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h5 : Real.log R ^ 5 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hraw' : (∫ t in (0 : ℝ)..R,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      16 * Real.log R ^ 4 + 1024 * Real.log R ^ 8 + 512 * Real.log R ^ 5 := by
    calc
      _ ≤ _ := hraw
      _ = R * (16 / ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 4)) +
          1024 * Real.log R ^ 8 + 512 * Real.log R ^ 5 := by field_simp <;> ring
      _ ≤ _ := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  linarith

theorem exists_mollifier_optimized_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → 2 ≤ Real.log R →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 → ∀ σ : ℝ, σ₀ ≤ σ →
      (∫ t in (1 : ℝ)..R,
        ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  obtain ⟨K, hK, hinner⟩ := exists_mollifier_optimized_interior_bound
  refine ⟨max K 1552, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro R hR hlog σ₀ hσ₀ hσ₀1 σ hσ
  by_cases hcut : σ ≤ 1 + 1 / Real.log R
  · exact (hinner R hR hlog σ₀ hσ₀ hσ₀1 σ hσ hcut).trans
      (by gcongr; exact le_max_left _ _)
  · have hh := mollifier_optimized_right_bound hR hlog (le_of_not_ge hcut)
    have hp : 1 ≤ R ^ ((11 / 4 : ℝ) * (1 - σ₀)) :=
      Real.one_le_rpow hR (by positivity)
    apply hh.trans
    calc
      _ ≤ (max K 1552) * Real.log R ^ 9 := by gcongr; exact le_max_right _ _
      _ ≤ _ := by
        have hconst : 0 ≤ max K 1552 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hp
          (mul_nonneg hconst (show 0 ≤ Real.log R ^ 9 by positivity))]

end Sidon
