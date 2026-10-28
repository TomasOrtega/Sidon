module

public import Sidon.Analysis.SmoothingOptimization

@[expose] public section

/-! # Optimizing the regular Bohr-set boundary error -/

noncomputable section

namespace Sidon

theorem regular_bohr_optimization {d : ℕ} (hd : 0 < d) {X C E ρ : ℝ}
    (hX : X ≤ 1) (hC : 1 ≤ C) (hE : 0 < E) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ ρ / (100 * (d : ℝ)) →
      X ≤ C * (t⁻¹) ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) +
        100 * (d : ℝ) * (t / ρ)) :
    X ≤ (100 + C) * ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hCpos : 0 ≤ C := by linarith
  have hratio : 1 ≤ (d : ℝ) / ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hexp : 0 ≤ 1 / (14 * (d : ℝ)) := by positivity
  by_cases hElarge : 1 ≤ E
  · have hpow := Real.one_le_rpow hElarge hexp
    have hprod : 1 ≤ ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (d : ℝ) / ρ)]
    have hcprod := mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 100 + C)
    nlinarith
  · have hEsmall : E ≤ 1 := (lt_of_not_ge hElarge).le
    let t : ℝ := E ^ (3 / (40 * (d : ℝ)))
    have ht : 0 < t := Real.rpow_pos_of_pos hE _
    have htq : t ≤ E ^ (1 / (14 * (d : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_ge hE hEsmall
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 14 * d)
        (by positivity : (0 : ℝ) < 40 * d)).mpr
      nlinarith
    by_cases hsmall : t ≤ ρ / (100 * (d : ℝ))
    · have hb := hbound t ht hsmall
      have heq : (t⁻¹) ^ (2 / 3 : ℝ) * E ^ (1 / (8 * (d : ℝ))) = t := by
        dsimp only [t]
        rw [← Real.rpow_neg hE.le, ← Real.rpow_mul hE.le, ← Real.rpow_add hE]
        congr 1
        field_simp
        ring
      rw [mul_assoc C, heq] at hb
      have hfactor : C * t ≤ C * ((d : ℝ) / ρ) * t := by
        nlinarith [mul_le_mul_of_nonneg_left hratio (mul_nonneg hCpos ht.le)]
      have hterm : 100 * (d : ℝ) * (t / ρ) = 100 * ((d : ℝ) / ρ) * t := by ring
      rw [hterm] at hb
      calc
        X ≤ (100 + C) * ((d : ℝ) / ρ) * t := by nlinarith [hb]
        _ ≤ _ := mul_le_mul_of_nonneg_left htq (by positivity)
    · have hlarge : ρ / (100 * (d : ℝ)) < t := lt_of_not_ge hsmall
      have hlarge' : ρ < t * (100 * (d : ℝ)) :=
        (div_lt_iff₀ (by positivity : (0 : ℝ) < 100 * d)).mp hlarge
      have hqt : 1 ≤ 100 * ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) := by
        have heq : 100 * ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) =
            (E ^ (1 / (14 * (d : ℝ))) * (100 * d)) / ρ := by ring
        rw [heq]
        apply (le_div_iff₀ hρ).mpr
        simpa only [one_mul] using (le_of_lt hlarge').trans
          (mul_le_mul_of_nonneg_right htq (by positivity : (0 : ℝ) ≤ 100 * d))
      have hrest : 0 ≤ C * ((d : ℝ) / ρ) * E ^ (1 / (14 * (d : ℝ))) := by positivity
      nlinarith

end Sidon
