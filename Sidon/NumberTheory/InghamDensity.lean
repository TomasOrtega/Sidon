import Sidon.NumberTheory.JensenZeroDensity
import Sidon.NumberTheory.ZetaCrudeCount

/-! # Uniform zero density from optimized mollifier slices -/

noncomputable section

open Set MeasureTheory Real

namespace Sidon

theorem rpow_logarithmic_shift {T : ℝ} (hT : 1 < T) (a σ : ℝ) :
    T ^ (a * (1 - (σ - 1 / Real.log T))) =
      Real.exp a * T ^ (a * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem crude_rpow_le_density_scale {T σ A : ℝ} (hT : 1 < T)
    (hA : (8 / 3 : ℝ) ≤ A) (hσ : σ ≤ 1 / 2 + 1 / Real.log T) :
    T ^ (4 / 3 : ℝ) ≤ Real.exp A * T ^ (A * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hσ' := mul_le_mul_of_nonneg_right hσ hlog.le
  rw [add_mul, div_mul_cancel₀ _ hlog.ne'] at hσ'
  have hA0 : 0 ≤ A := by linarith
  have hh := mul_le_mul_of_nonneg_left hσ' hA0
  have hhalf := mul_le_mul_of_nonneg_right hA hlog.le
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem jensen_center_loss_le {N : ℕ} {T : ℝ} (hT : 0 < T) (hN : T ≤ N) :
    (T - 2) * (131072 / (N : ℝ)) ≤ 131072 := by
  have hN0 : (0 : ℝ) < N := hT.trans_le hN
  calc
    _ ≤ (N : ℝ) * (131072 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

theorem exists_uniformZeroDensity_of_mollifier_slices {K T₀ : ℝ} (hK : 0 < K)
    (hslices : ∀ T : ℝ, T₀ ≤ T → ∀ σ₀ : ℝ, (1 / 2 : ℝ) ≤ σ₀ → σ₀ ≤ 1 →
      ∃ N : ℕ, 131072 ≤ N ∧ T ≤ (N : ℝ) ∧
        ∀ u ∈ Icc σ₀ (4 - σ₀),
          (∫ t in Icc 1 (T + 3), ‖mollifierError N ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
            K * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) * (Real.log T) ^ 9) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : ℝ, UniformZetaZeroDensity (23 / 8) 11 C U := by
  obtain ⟨D, hD, hcrude⟩ := zetaZeroCount_zero_le_fourThirds
  let Z : ℝ := zetaZeroCount 0 4
  let H : ℝ := Z + 2 * (K * Real.exp (11 / 4) + 131072)
  let C : ℝ := D * Real.exp (23 / 8) + H
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max T₀ (Real.exp 4), ?_⟩
  intro T hT σ hσ0 hσ1
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hexp : Real.exp 4 ≤ T := (le_max_right _ _).trans hT
  have hexp5 : (5 : ℝ) ≤ Real.exp 4 := by
    have hh := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT1 : 1 < T := by linarith
  have hTpos : 0 < T := by linarith
  have hT3 : 3 ≤ T := by linarith
  have hlog : 4 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 4) hexp
    simpa only [Real.log_exp] using hh
  let ℓ := Real.log T
  let ε : ℝ := 1 / ℓ
  let X : ℝ := T ^ ((23 / 8 : ℝ) * (1 - σ))
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓpos : 0 < ℓ := by linarith
  have hε : 0 < ε := one_div_pos.mpr hℓpos
  have hεquarter : ε ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hX : 1 ≤ X := Real.one_le_rpow hT1.le (by nlinarith)
  have hℓ9 : 1 ≤ ℓ ^ 9 := one_le_pow₀ hℓ
  have hℓ11 : 1 ≤ ℓ ^ 11 := one_le_pow₀ hℓ
  have hscale : 1 ≤ X * ℓ ^ 11 := one_le_mul_of_one_le_of_one_le hX hℓ11
  by_cases hlow : σ ≤ 1 / 2 + ε
  · have hc0 : (zetaZeroCount σ T : ℝ) ≤ D * T ^ (4 / 3 : ℝ) := by
      exact (Nat.cast_le.mpr (zetaZeroCount_antitone T hσ0)).trans (hcrude T hT1.le)
    have hp := crude_rpow_le_density_scale hT1 (A := 23 / 8) (by norm_num) hlow
    calc
      _ ≤ D * T ^ (4 / 3 : ℝ) := hc0
      _ ≤ D * (Real.exp (23 / 8) * X) := mul_le_mul_of_nonneg_left hp hD.le
      _ ≤ C * X * ℓ ^ 11 := by
        have hDC : D * Real.exp (23 / 8) ≤ C := by dsimp [C]; linarith
        calc
          _ = (D * Real.exp (23 / 8)) * X := by ring
          _ ≤ C * X := mul_le_mul_of_nonneg_right hDC (by positivity)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hℓ11
  · let σ₀ : ℝ := σ - ε
    have hσ₀ : (1 / 2 : ℝ) ≤ σ₀ := by dsimp [σ₀]; linarith
    have hσ₀1 : σ₀ ≤ 1 := by dsimp [σ₀]; linarith
    obtain ⟨N, hN, hNT, hslice⟩ := hslices T hT₀ σ₀ hσ₀ hσ₀1
    let S := (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im)
    have hmass := jensen_zero_occurrences_bound hN hσ₀ hσ₀1 hε.le hεquarter hT3 S
      (Finset.filter_subset _ _) (fun z hz => by
        have hh := (Finset.mem_filter.mp hz).2.1
        simpa only [σ₀, sub_add_cancel] using hh)
      (fun z hz => (Finset.mem_filter.mp hz).2.2) hslice
    have hpower : T ^ ((11 / 4 : ℝ) * (1 - σ₀)) ≤ Real.exp (11 / 4) * X := by
      rw [rpow_logarithmic_shift hT1]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      nlinarith
    have hmajor : (S.card : ℝ) * (2 * ε ^ 2 / 3) ≤
        K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072 := by
      apply hmass.trans
      apply add_le_add
      · have hh := mul_le_mul_of_nonneg_left hpower hK.le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (pow_nonneg hℓpos.le 9)
      · exact jensen_center_loss_le hTpos hNT
    have hidentity : (S.card : ℝ) = (3 / 2 : ℝ) * ℓ ^ 2 *
        ((S.card : ℝ) * (2 * ε ^ 2 / 3)) := by
      dsimp [ε]
      field_simp
    have hcard : (S.card : ℝ) ≤ 2 * ℓ ^ 2 *
        (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) := by
      calc
        _ = _ := hidentity
        _ ≤ (3 / 2 : ℝ) * ℓ ^ 2 *
            (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) :=
          mul_le_mul_of_nonneg_left hmajor (by positivity)
        _ ≤ _ := by gcongr; norm_num
    have hcount : (zetaZeroCount σ T : ℝ) ≤ Z + (S.card : ℝ) := by
      dsimp [Z, S]
      exact_mod_cast zetaZeroCount_le_low_add_high σ T
    have hℓ2 : ℓ ^ 2 ≤ X * ℓ ^ 11 := by
      have hp : ℓ ^ 11 = ℓ ^ 2 * ℓ ^ 9 := by ring
      rw [hp]
      have hh := mul_le_mul_of_nonneg_left hℓ9 (sq_nonneg ℓ)
      nlinarith
    have hZscale : Z ≤ Z * X * ℓ ^ 11 := by nlinarith
    have hHle : H ≤ C := by
      dsimp [C]
      have hh : 0 ≤ D * Real.exp (23 / 8) := by positivity
      linarith
    calc
      _ ≤ Z + (S.card : ℝ) := hcount
      _ ≤ Z + 2 * ℓ ^ 2 * (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) := by
        linarith
      _ = Z + 2 * (K * Real.exp (11 / 4)) * X * ℓ ^ 11 + 262144 * ℓ ^ 2 := by ring
      _ ≤ Z * X * ℓ ^ 11 + 2 * (K * Real.exp (11 / 4)) * X * ℓ ^ 11 +
          262144 * (X * ℓ ^ 11) := by linarith
      _ = H * X * ℓ ^ 11 := by dsimp [H]; ring
      _ ≤ C * X * ℓ ^ 11 := by gcongr

end Sidon
