import Sidon.NumberTheory.LogarithmicReserve
import Sidon.NumberTheory.ZetaZeroCount
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovSummedZeroFree

/-! # Uniform zero-free widths from high-ordinate margins -/

noncomputable section

open Filter Topology

namespace Sidon

theorem logarithmicZeroFreeWidth_nonneg {C : ℝ} (hC : 0 ≤ C) {T : ℝ}
    (hT : 1 < Real.log T) : 0 ≤ logarithmicZeroFreeWidth C T :=
  div_nonneg hC (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (Real.log_pos hT).le _))

theorem logarithmicZeroFreeWidth_pos {C T : ℝ} (hC : 0 < C)
    (hT : 1 < Real.log T) : 0 < logarithmicZeroFreeWidth C T := by
  exact div_pos hC (mul_pos
    (Real.rpow_pos_of_pos (by linarith : 0 < Real.log T) _)
    (Real.rpow_pos_of_pos (Real.log_pos hT) _))

theorem logarithmicZeroFreeWidth_antitone {C a b : ℝ} (hC : 0 ≤ C)
    (ha : 0 < a) (hlog : 1 < Real.log a) (hab : a ≤ b) :
    logarithmicZeroFreeWidth C b ≤ logarithmicZeroFreeWidth C a := by
  have hablog := Real.log_le_log ha hab
  have habloglog := Real.log_le_log (by linarith : 0 < Real.log a) hablog
  apply div_le_div_of_nonneg_left hC
    (mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < Real.log a) _)
      (Real.rpow_pos_of_pos (Real.log_pos hlog) _))
  exact mul_le_mul (Real.rpow_le_rpow (by linarith) hablog (by norm_num))
    (Real.rpow_le_rpow (Real.log_pos hlog).le habloglog (by norm_num))
    (Real.rpow_nonneg (Real.log_pos hlog).le _)
    (Real.rpow_nonneg (by linarith : 0 ≤ Real.log b) _)

theorem tendsto_logarithmicZeroFreeWidth_zero (C : ℝ) :
    Tendsto (logarithmicZeroFreeWidth C) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp Real.tendsto_log_atTop
  have h₂ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  exact (h₁.atTop_mul_atTop₀ h₂).const_div_atTop C

theorem logarithmicZeroFreeWidth_shift_le {C T : ℝ} (hC : 0 ≤ C)
    (hT : 2 ≤ T) (hlog : 2 ≤ Real.log T) :
    logarithmicZeroFreeWidth (C / 2) T ≤ logarithmicZeroFreeWidth C (T + 2) := by
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := by linarith
  have hloglog : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have hshift : T + 2 ≤ T ^ 2 := by nlinarith
  have h₁ : Real.log (T + 2) ≤ 2 * Real.log T := by
    have hh := Real.log_le_log (by linarith : 0 < T + 2) hshift
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have h₂ : Real.log (Real.log (T + 2)) ≤ 2 * Real.log (Real.log T) := by
    have hla : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
    have hh := Real.log_le_log hla h₁
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog0.ne'] at hh
    have hh₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlog
    linarith
  have hp₁ := Real.rpow_le_rpow (Real.log_pos (by linarith : 1 < T + 2)).le h₁
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hslog : 1 < Real.log (T + 2) :=
    (show (1 : ℝ) < Real.log T by linarith).trans_le
      (Real.log_le_log hT0 (by linarith : T ≤ T + 2))
  have hp₂ := Real.rpow_le_rpow (Real.log_pos hslog).le h₂
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hprod := mul_le_mul hp₁ hp₂
    (Real.rpow_nonneg (Real.log_pos hslog).le _)
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.log T) _)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlog0.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hloglog.le] at hprod
  have hpow : (2 : ℝ) ^ ((2 : ℝ) / 3) * 2 ^ ((1 : ℝ) / 3) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hden : (Real.log (T + 2)) ^ ((2 : ℝ) / 3) *
      (Real.log (Real.log (T + 2))) ^ ((1 : ℝ) / 3) ≤
      2 * ((Real.log T) ^ ((2 : ℝ) / 3) *
        (Real.log (Real.log T)) ^ ((1 : ℝ) / 3)) := by
    calc
      _ ≤ _ := hprod
      _ = _ := by rw [show (2 : ℝ) ^ ((2 : ℝ) / 3) * (Real.log T) ^ ((2 : ℝ) / 3) *
          (2 ^ ((1 : ℝ) / 3) * (Real.log (Real.log T)) ^ ((1 : ℝ) / 3)) =
        (2 ^ ((2 : ℝ) / 3) * 2 ^ ((1 : ℝ) / 3)) *
          ((Real.log T) ^ ((2 : ℝ) / 3) * (Real.log (Real.log T)) ^ ((1 : ℝ) / 3)) by ring, hpow]
  change C / 2 / _ ≤ C / _
  rw [div_div]
  exact div_le_div_of_nonneg_left hC (by
    exact mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (T + 2)) _)
      (Real.rpow_pos_of_pos (by
        exact Real.log_pos ((show (1 : ℝ) < Real.log T by linarith).trans_le
          (Real.log_le_log hT0 (by linarith : T ≤ T + 2)))) _)) (by simpa only [mul_comm] using hden)

theorem exists_logarithmicZeroFreeWidth_of_height_margin {C U : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hUlog : 1 < Real.log (U + 2))
    (hmargin : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → U ≤ ρ.im →
      ρ.re ≤ 1 - logarithmicZeroFreeWidth C (ρ.im + 2)) :
    ∃ T₀ : ℝ, ZetaZeroFreeWidth (logarithmicZeroFreeWidth (C / 2)) T₀ := by
  have hsmall : ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ criticalZetaZeros U,
      logarithmicZeroFreeWidth (C / 2) T < 1 - ρ.re := by
    apply (eventually_all_finset (criticalZetaZeros U)).mpr
    intro ρ hρ
    have hz := (mem_criticalZetaZeros.mp hρ).1
    have hre : ρ.re < 1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hz)
    exact (tendsto_logarithmicZeroFreeWidth_zero (C / 2)).eventually_lt_const (by linarith)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (hsmall.and ((eventually_ge_atTop (2 : ℝ)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ))))
  refine ⟨T₀, ?_⟩
  intro T hT z hz
  obtain ⟨hsmallT, hT2, hlogT⟩ := hT₀ T hT
  have hρ := mem_criticalZetaZeros.mp (mem_zetaZeroOccurrences.mp hz).1
  by_cases hlow : z.1.im ≤ U
  · have hρU : z.1 ∈ criticalZetaZeros U := mem_criticalZetaZeros.mpr
      ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hlow⟩
    linarith [hsmallT z.1 hρU]
  · have hhigh : U ≤ z.1.im := le_of_lt (lt_of_not_ge hlow)
    have hright := hmargin z.1 hρ.1 hρ.2.1 hρ.2.2.1 hhigh
    have hshift := logarithmicZeroFreeWidth_shift_le hC.le hT2 hlogT
    have hmono := logarithmicZeroFreeWidth_antitone hC.le
      (by linarith : 0 < z.1.im + 2)
      (hUlog.trans_le (Real.log_le_log (by linarith : 0 < U + 2) (by linarith)))
      (show z.1.im + 2 ≤ T + 2 by linarith [hρ.2.2.2.2])
    linarith

theorem exists_logarithmicZetaZeroFreeWidth :
    ∃ T₀ : ℝ, ZetaZeroFreeWidth (logarithmicZeroFreeWidth (1 / 20000)) T₀ := by
  have hC : (0 : ℝ) < 1 / 10000 := by norm_num
  have hClim : (1 / 10000 : ℝ) <
      RiemannGaussian.ZetaVinogradovSummedZeroFree.coefficientLimit := by
    unfold RiemannGaussian.ZetaVinogradovSummedZeroFree.coefficientLimit
    have hp := Real.pi_gt_three
    linarith
  obtain ⟨U₀, hU₀, hmargin⟩ :=
    RiemannGaussian.ZetaVinogradovSummedZeroFree.exists_eventual_strip hC hClim
  let U : ℝ := max U₀ (Real.exp 2)
  have hU : 0 < U := (Real.exp_pos 2).trans_le (le_max_right _ _)
  have hUlog : 1 < Real.log (U + 2) := by
    have hh : Real.exp 2 < U + 2 := by
      have := le_max_right U₀ (Real.exp 2)
      change Real.exp 2 ≤ U at this
      linarith
    have := (Real.lt_log_iff_exp_lt (by linarith : 0 < U + 2)).mpr hh
    linarith
  have hhigh : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → U ≤ ρ.im →
      ρ.re ≤ 1 - logarithmicZeroFreeWidth (1 / 10000) (ρ.im + 2) := by
    intro ρ hz hρ0 hρ1 hheight
    have him : 0 < ρ.im := hU.trans_le hheight
    have hnontrivial : RiemannGaussian.IsNontrivialZetaZero ρ := by
      refine ⟨hz, ?_, ?_⟩
      · rintro ⟨n, he⟩
        have hh := congrArg Complex.im he
        simp at hh
        linarith
      · intro he
        subst ρ
        exact riemannZeta_one_ne_zero hz
    have hlarge : U₀ ≤ |ρ.im| := by
      rw [abs_of_pos him]
      exact (le_max_left U₀ (Real.exp 2)).trans hheight
    have hh := (hmargin ⟨ρ, hnontrivial⟩ hlarge).2
    have hwidth : RiemannGaussian.ZetaVinogradovBalancedScale.width (1 / 10000) ρ.im =
        logarithmicZeroFreeWidth (1 / 10000) (ρ.im + 2) := by
      simp only [RiemannGaussian.ZetaVinogradovBalancedScale.width,
        RiemannGaussian.ZetaVinogradovBalancedScale.level,
        RiemannGaussian.ZetaNearOneBudgetLimit.scale,
        RiemannGaussian.ZetaNearOneLogProfile.height, abs_of_pos him,
        logarithmicZeroFreeWidth]
    change ρ.re < 1 - RiemannGaussian.ZetaVinogradovBalancedScale.width (1 / 10000) ρ.im at hh
    rw [hwidth] at hh
    exact hh.le
  simpa only [show (1 / 10000 : ℝ) / 2 = 1 / 20000 by norm_num] using
    exists_logarithmicZeroFreeWidth_of_height_margin hC hU hUlog hhigh


end Sidon
