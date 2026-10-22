import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Dimension-uniform optimization of a compact smoothing estimate -/

noncomputable section

namespace Sidon

theorem compact_smoothing_optimization {d : ℕ} (hd : 0 < d) {X K R : ℝ}
    (hX : X ≤ 1) (hK : 1 ≤ K) (hR : 0 < R)
    (hbound : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      X ≤ 2 * K * η + R * (10 / η) ^ d) :
    X ≤ 30 * K ^ ((d : ℝ) / (d + 1)) * R ^ (1 / (d + 1 : ℝ)) := by
  have hKpos : 0 < K := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  let z : ℝ := (R / K) ^ (1 / ((d : ℝ) + 1))
  have hz : 0 < z := Real.rpow_pos_of_pos (div_pos hR hKpos) _
  have hzpow : z ^ (d + 1) = R / K := by
    dsimp only [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hR hKpos).le]
    have hexp : (1 / ((d : ℝ) + 1)) * (↑(d + 1) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]
  have hbalance : R / z ^ d = K * z := by
    apply (div_eq_iff (pow_ne_zero _ hz.ne')).mpr
    have hzpow' : z ^ d * z = R / K := by simpa only [pow_succ] using hzpow
    have hh := (eq_div_iff hKpos.ne').mp hzpow'
    nlinarith
  have hshape : K * z = K ^ ((d : ℝ) / (d + 1)) * R ^ (1 / (d + 1 : ℝ)) := by
    dsimp only [z]
    rw [Real.div_rpow hR.le hKpos.le]
    have hexp : (d : ℝ) / (d + 1) = 1 - 1 / (d + 1) := by field_simp; ring
    rw [hexp, Real.rpow_sub hKpos, Real.rpow_one]
    ring
  have hmain : X ≤ 30 * (K * z) := by
    by_cases hsmall : 10 * z ≤ 1 / 2
    · have hb := hbound (10 * z) (by positivity) hsmall
      have hterm : R * (10 / (10 * z)) ^ d = K * z := by
        have hdiv : 10 / (10 * z) = z⁻¹ := by field_simp
        rw [hdiv, inv_pow, ← div_eq_mul_inv, hbalance]
      rw [hterm] at hb
      nlinarith [mul_pos hKpos hz]
    · have hlarge : 1 < 20 * z := by linarith
      have hKz : z ≤ K * z := le_mul_of_one_le_left hz.le hK
      linarith
  rw [hshape] at hmain
  simpa only [mul_assoc] using hmain

theorem rpow_product_le_of_product_le_one {K E a b c e : ℝ}
    (hK : 1 ≤ K) (hE : 0 < E) (he : 0 < e) (heb : e ≤ b)
    (habc : a * e ≤ b * c) (hprod : K ^ c * E ^ e ≤ 1) :
    K ^ a * E ^ b ≤ K ^ c * E ^ e := by
  have hKpos : 0 < K := by linarith
  have hθ : 1 ≤ b / e := (le_div_iff₀ he).mpr (by linarith)
  have hexp : a - c * (b / e) ≤ 0 := by
    have hh := (le_div_iff₀ he).mpr habc
    have heq : b * c / e = c * (b / e) := by ring
    rw [heq] at hh
    linarith
  have hfactor : K ^ (a - c * (b / e)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK hexp
  have hbase : 0 < K ^ c * E ^ e := by positivity
  have hpower : (K ^ c * E ^ e) ^ (b / e) ≤ K ^ c * E ^ e := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hbase hprod hθ
  have heq : K ^ a * E ^ b = K ^ (a - c * (b / e)) *
      (K ^ c * E ^ e) ^ (b / e) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hKpos.le c) (Real.rpow_nonneg hE.le e),
      ← Real.rpow_mul hKpos.le,
      ← Real.rpow_mul hE.le, Real.rpow_sub hKpos]
    have heqexp : e * (b / e) = b := by field_simp
    rw [heqexp]
    have hkpow : K ^ (c * (b / e)) ≠ 0 := (Real.rpow_pos_of_pos hKpos _).ne'
    field_simp
  rw [heq]
  calc
    _ ≤ 1 * (K ^ c * E ^ e) :=
      mul_le_mul hfactor hpower (Real.rpow_nonneg hbase.le _) zero_le_one
    _ = _ := one_mul _

theorem smoothing_exponent_comparison {d : ℕ} (hd : 0 < d) {K E : ℝ}
    (hK : 1 ≤ K) (hE : 0 < E) (hprod : K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) ≤ 1) :
    K ^ ((d : ℝ) / (d + 1)) * E ^ (1 / (2 * (d + 1 : ℝ))) ≤
      K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply rpow_product_le_of_product_le_one hK hE (by positivity) _ _ hprod
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * d)
      (by positivity : (0 : ℝ) < 2 * (d + 1))).mpr
    nlinarith
  · have hdp : (0 : ℝ) < d := by linarith
    have hsucc : (0 : ℝ) < d + 1 := by linarith
    have ha : (d : ℝ) / (d + 1) * (1 / (8 * (d : ℝ))) = 1 / (8 * (d + 1)) := by
      field_simp
    have hb : (1 / (2 * (d + 1 : ℝ))) * (2 / 3) = 1 / (3 * (d + 1)) := by
      field_simp
    rw [ha, hb]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (d + 1))
      (by positivity : (0 : ℝ) < 3 * (d + 1))).mpr
    nlinarith

theorem compact_smoothing_paper_bound {d : ℕ} (hd : 0 < d) {X K E : ℝ}
    (hX : X ≤ 1) (hK : 1 ≤ K) (hE : 0 < E)
    (hbound : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      X ≤ 2 * K * η + (1600 * Real.sqrt E) * (10 / η) ^ d) :
    X ≤ 48000 * K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) := by
  have hKpos : 0 < K := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hrecip : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
  have hreciple : 1 / ((d : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hdpos).mpr
    have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hc : (1600 : ℝ) ^ (1 / ((d : ℝ) + 1)) ≤ 1600 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 1600) hreciple
  have hpow : (1600 * Real.sqrt E) ^ (1 / ((d : ℝ) + 1)) ≤
      1600 * E ^ (1 / (2 * (d + 1 : ℝ))) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1600) (Real.sqrt_nonneg E),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hE.le]
    have heq : (1 / 2 : ℝ) * (1 / ((d : ℝ) + 1)) = 1 / (2 * (d + 1 : ℝ)) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hE.le _)
  by_cases hsmall : K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) ≤ 1
  · have hb := compact_smoothing_optimization hd hX hK (by positivity) hbound
    have hstep := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ 30 * K ^ ((d : ℝ) / (d + 1)))
    have hcomp := smoothing_exponent_comparison hd hK hE hsmall
    have hcomp' := mul_le_mul_of_nonneg_left hcomp (by norm_num : (0 : ℝ) ≤ 48000)
    calc
      X ≤ 30 * K ^ ((d : ℝ) / (d + 1)) *
          (1600 * E ^ (1 / (2 * (d + 1 : ℝ)))) := hb.trans hstep
      _ = 48000 * (K ^ ((d : ℝ) / (d + 1)) * E ^ (1 / (2 * (d + 1 : ℝ)))) := by ring
      _ ≤ _ := hcomp'
      _ = _ := by ring
  · have hlarge : 1 < K ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) := lt_of_not_ge hsmall
    nlinarith

end Sidon
