import Sidon.Analysis.Approximation.Polynomial
import Sidon.Analysis.Approximation.Interpolation
import Sidon.Analysis.Approximation.SignedWeights
import Sidon.Equidistribution.Bohr
import Sidon.Transference.PositiveMax

/-! # Finite moment matching and the obstruction to uniform bandwidth -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.BandwidthCounterexample

def maxCoordinateTent {d : ℕ} (ρ : ℝ) (β : Fin d → AddCircle (1 : ℝ)) : ℝ :=
  positiveMax (fun i => ρ - ‖β i‖)

theorem maxCoordinateTent_nonneg {d : ℕ} (ρ : ℝ) (β : Fin d → AddCircle (1 : ℝ)) :
    0 ≤ maxCoordinateTent ρ β := positiveMax_nonneg _

theorem maxCoordinateTent_le {d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (β : Fin d → AddCircle (1 : ℝ)) : maxCoordinateTent ρ β ≤ ρ := by
  apply positiveMax_le hρ
  intro i
  exact sub_le_self _ (norm_nonneg _)

theorem maxCoordinateTent_eq_of_zero {d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {β : Fin d → AddCircle (1 : ℝ)} {i : Fin d} (hi : β i = 0) :
    maxCoordinateTent ρ β = ρ := by
  apply le_antisymm (maxCoordinateTent_le hρ β)
  change ρ ≤ positiveMax (fun j => ρ - ‖β j‖)
  have hh : ρ - ‖β i‖ ≤ positiveMax (fun j => ρ - ‖β j‖) :=
    le_positiveMax (fun j => ρ - ‖β j‖) i
  simpa only [hi, norm_zero, sub_zero] using hh

theorem maxCoordinateTent_eq_zero {d : ℕ} {ρ : ℝ} {β : Fin d → AddCircle (1 : ℝ)}
    (hβ : ∀ i, ρ ≤ ‖β i‖) : maxCoordinateTent ρ β = 0 := by
  apply le_antisymm _ (maxCoordinateTent_nonneg _ _)
  apply positiveMax_le le_rfl
  intro i
  exact sub_nonpos.mpr (hβ i)

theorem lipschitzWith_maxCoordinateTent {d : ℕ} (ρ : ℝ) :
    LipschitzWith 1 (maxCoordinateTent (d := d) ρ) := by
  have hbound (β γ : Fin d → AddCircle (1 : ℝ)) :
      maxCoordinateTent ρ β ≤ maxCoordinateTent ρ γ + dist β γ := by
    apply positiveMax_le (add_nonneg (maxCoordinateTent_nonneg _ _) dist_nonneg)
    intro i
    have hh : ρ - ‖γ i‖ ≤ maxCoordinateTent ρ γ :=
      le_positiveMax (fun j => ρ - ‖γ j‖) i
    have hn := norm_sub_norm_le (γ i) (β i)
    have hpi := dist_le_pi_dist γ β i
    rw [dist_eq_norm] at hpi
    have hnorm : ‖γ i‖ - ‖β i‖ ≤ dist β γ := by
      exact hn.trans (by simpa only [← dist_eq_norm, dist_comm] using hpi)
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro β γ
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_le.mpr ⟨by linarith [hbound γ β, dist_comm β γ], by linarith [hbound β γ]⟩

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def productAverage (d : ℕ) (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) : ℂ :=
  ∑ x : Fin d → ι, ((∏ i, w (x i) : ℝ) : ℂ) * F (fun i => t (x i))

theorem sum_product_weights (d : ℕ) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    (∑ x : Fin d → ι, ∏ i, w (x i)) = 1 := by
  rw [← Fintype.sum_pow, hw, one_pow]

theorem productAverage_character (d : ℕ) (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (n : Fin d → ℤ) :
    productAverage d w t (torusCharacter n) =
      ∏ j : Fin d, ∑ i, (w i : ℂ) * fourier (n j) (t i) := by
  classical
  simp only [productAverage, torusCharacter_apply, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib, Fintype.prod_sum]

theorem productAverage_polynomial {d : ℕ} (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (a : (Fin d → ℤ) →₀ ℂ) :
    productAverage d w t (torusPolynomial a) =
      ∑ n ∈ a.support, a n * productAverage d w t (torusCharacter n) := by
  classical
  simp only [productAverage, torusPolynomial_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem productAverage_polynomial_eq_of_moments {d M : ℕ}
    (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (v : κ → ℝ) (u : κ → AddCircle (1 : ℝ))
    (hmom : ∀ n : ℤ, |n| ≤ M → (∑ i, (w i : ℂ) * fourier n (t i)) =
      ∑ j, (v j : ℂ) * fourier n (u j))
    (a : (Fin d → ℤ) →₀ ℂ) (ha : HasTorusBandwidth a M) :
    productAverage d w t (torusPolynomial a) = productAverage d v u (torusPolynomial a) := by
  rw [productAverage_polynomial, productAverage_polynomial]
  apply Finset.sum_congr rfl
  intro n hn
  rw [productAverage_character, productAverage_character]
  congr 1
  exact Finset.prod_congr rfl fun j _ => hmom (n j) (ha n hn j)

theorem norm_productAverage_sub_le {d : ℕ} (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (F G : (Fin d → AddCircle (1 : ℝ)) → ℂ) {ε : ℝ}
    (hFG : ∀ β, ‖F β - G β‖ ≤ ε) :
    ‖productAverage d w t F - productAverage d w t G‖ ≤ ε := by
  classical
  simp only [productAverage, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : Fin d → ι,
        ‖((∏ i, w (x i) : ℝ) : ℂ) * F (fun i => t (x i)) -
          ((∏ i, w (x i) : ℝ) : ℂ) * G (fun i => t (x i))‖ := norm_sum_le _ _
    _ ≤ ∑ x : Fin d → ι, (∏ i, w (x i)) * ε := by
      apply Finset.sum_le_sum
      intro x _
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg fun i _ => hw0 (x i))]
      exact mul_le_mul_of_nonneg_left (hFG _) (Finset.prod_nonneg fun i _ => hw0 (x i))
    _ = ε := by rw [← Finset.sum_mul, sum_product_weights d w hw, one_mul]

theorem norm_productAverage_sub_le_of_polynomial {d M : ℕ}
    (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (v : κ → ℝ) (u : κ → AddCircle (1 : ℝ))
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hv0 : ∀ j, 0 ≤ v j) (hv : ∑ j, v j = 1)
    (hmom : ∀ n : ℤ, |n| ≤ M → (∑ i, (w i : ℂ) * fourier n (t i)) =
      ∑ j, (v j : ℂ) * fourier n (u j))
    (a : (Fin d → ℤ) →₀ ℂ) (ha : HasTorusBandwidth a M)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) {ε : ℝ}
    (hF : ∀ β, ‖F β - torusPolynomial a β‖ ≤ ε) :
    ‖productAverage d w t F - productAverage d v u F‖ ≤ 2 * ε := by
  have heq := productAverage_polynomial_eq_of_moments w t v u hmom a ha
  have h₁ := norm_productAverage_sub_le w t hw0 hw F (torusPolynomial a) hF
  have h₂ := norm_productAverage_sub_le v u hv0 hv F (torusPolynomial a) hF
  rw [heq] at h₁
  have h₂' : ‖productAverage d v u (torusPolynomial a) - productAverage d v u F‖ ≤ ε := by
    simpa only [norm_sub_rev] using h₂
  calc
    _ = ‖(productAverage d w t F - productAverage d v u (torusPolynomial a)) +
        (productAverage d v u (torusPolynomial a) - productAverage d v u F)‖ := by
          congr 1
          ring
    _ ≤ ‖productAverage d w t F - productAverage d v u (torusPolynomial a)‖ +
        ‖productAverage d v u (torusPolynomial a) - productAverage d v u F‖ := by
      exact norm_add_le _ _
    _ ≤ ε + ε := add_le_add h₁ h₂'
    _ = _ := by ring

def realProductAverage (d : ℕ) (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (F : (Fin d → AddCircle (1 : ℝ)) → ℝ) : ℝ :=
  ∑ x : Fin d → ι, (∏ i, w (x i)) * F (fun i => t (x i))

theorem productAverage_ofReal (d : ℕ) (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (F : (Fin d → AddCircle (1 : ℝ)) → ℝ) :
    productAverage d w t (fun β => (F β : ℂ)) = (realProductAverage d w t F : ℂ) := by
  simp only [productAverage, realProductAverage, Complex.ofReal_sum, Complex.ofReal_mul]

theorem sum_weights_avoiding (w : ι → ℝ) (i₀ : ι) :
    (∑ i, if i = i₀ then 0 else w i) = (∑ i, w i) - w i₀ := by
  classical
  have heq (i : ι) : (if i = i₀ then 0 else w i) = w i - if i = i₀ then w i else 0 := by
    split_ifs <;> simp
  simp_rw [heq]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_product_weights_avoiding (d : ℕ) (w : ι → ℝ) (i₀ : ι) :
    (∑ x : Fin d → ι, (∏ j, w (x j)) * ∏ j, if x j = i₀ then (0 : ℝ) else 1) =
      ((∑ i, w i) - w i₀) ^ d := by
  classical
  calc
    _ = ∑ x : Fin d → ι, ∏ j, if x j = i₀ then 0 else w (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp
    _ = (∑ i, if i = i₀ then 0 else w i) ^ d := (Fintype.sum_pow (fun i : ι => if i = i₀ then (0 : ℝ) else w i) d).symm
    _ = _ := congrArg (fun y : ℝ => y ^ d) (sum_weights_avoiding w i₀)

theorem tent_average_lower_bound (d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (i₀ : ι) (ht : t i₀ = 0) :
    ρ * (1 - (1 - w i₀) ^ d) ≤ realProductAverage d w t (maxCoordinateTent ρ) := by
  classical
  have hpoint (x : Fin d → ι) :
      ρ * (1 - ∏ j, if x j = i₀ then (0 : ℝ) else 1) ≤
        maxCoordinateTent ρ (fun j => t (x j)) := by
    by_cases hx : ∃ j, x j = i₀
    · obtain ⟨j, hj⟩ := hx
      have hp : (∏ j, if x j = i₀ then (0 : ℝ) else 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_left hj)
      rw [hp, sub_zero, mul_one, maxCoordinateTent_eq_of_zero hρ (by rw [hj, ht])]
    · have hx' (j : Fin d) : x j ≠ i₀ := fun h => hx ⟨j, h⟩
      simp only [ite_eq_right (hx' _), Finset.prod_const_one, sub_self, mul_zero]
      exact maxCoordinateTent_nonneg _ _
  have hh : (∑ x : Fin d → ι, (∏ j, w (x j)) *
      (ρ * (1 - ∏ j, if x j = i₀ then (0 : ℝ) else 1))) ≤
        ∑ x : Fin d → ι, (∏ j, w (x j)) * maxCoordinateTent ρ (fun j => t (x j)) := by
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x)
      (Finset.prod_nonneg fun j _ => hw0 (x j))
  change _ ≤ realProductAverage d w t (maxCoordinateTent ρ) at hh
  apply le_trans (le_of_eq _) hh
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ x : Fin d → ι, (∏ j, w (x j)) * (ρ * 1)) = ρ := by
    rw [mul_one, ← Finset.sum_mul, sum_product_weights d w hw, one_mul]
  have hsecond : (∑ x : Fin d → ι,
      (∏ j, w (x j)) * (ρ * ∏ j, if x j = i₀ then (0 : ℝ) else 1)) =
        ρ * (1 - w i₀) ^ d := by
    have heq (x : Fin d → ι) :
        (∏ j, w (x j)) * (ρ * ∏ j, if x j = i₀ then (0 : ℝ) else 1) =
          ρ * ((∏ j, w (x j)) * ∏ j, if x j = i₀ then (0 : ℝ) else 1) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, sum_product_weights_avoiding, hw]
  rw [hfirst, hsecond]
  ring

theorem tent_average_eq_zero (d : ℕ) {ρ : ℝ}
    (v : κ → ℝ) (u : κ → AddCircle (1 : ℝ)) (hu : ∀ i, ρ ≤ ‖u i‖) :
    realProductAverage d v u (maxCoordinateTent ρ) = 0 := by
  unfold realProductAverage
  apply Finset.sum_eq_zero
  intro x _
  rw [maxCoordinateTent_eq_zero (fun j => hu (x j)), mul_zero]

theorem exists_dimension_obstruction_of_matching_moments {M : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (w : ι → ℝ) (t : ι → AddCircle (1 : ℝ))
    (v : κ → ℝ) (u : κ → AddCircle (1 : ℝ))
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hv0 : ∀ j, 0 ≤ v j) (hv : ∑ j, v j = 1)
    (i₀ : ι) (hwi : 0 < w i₀) (ht : t i₀ = 0) (hu : ∀ j, ρ ≤ ‖u j‖)
    (hmom : ∀ n : ℤ, |n| ≤ M → (∑ i, (w i : ℂ) * fourier n (t i)) =
      ∑ j, (v j : ℂ) * fourier n (u j)) :
    ∃ d : ℕ, 0 < d ∧ ∀ a : (Fin d → ℤ) →₀ ℂ, HasTorusBandwidth a M →
      ¬ ∀ β, ‖(maxCoordinateTent ρ β : ℂ) - torusPolynomial a β‖ ≤ ρ / 4 := by
  have hwi_le : w i₀ ≤ 1 := by
    simpa only [hw] using
      (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hw0 i) (Finset.mem_univ i₀))
  have hbase0 : 0 ≤ 1 - w i₀ := by linarith
  have hbase1 : 1 - w i₀ < 1 := by linarith
  have hsmall : ∀ᶠ d : ℕ in Filter.atTop, (1 - w i₀) ^ d < 1 / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨D + 1, by omega, ?_⟩
  intro a ha happ
  have hbound := norm_productAverage_sub_le_of_polynomial w t v u hw0 hw hv0 hv
    hmom a ha (fun β => (maxCoordinateTent ρ β : ℂ)) happ
  rw [productAverage_ofReal, productAverage_ofReal,
    tent_average_eq_zero (D + 1) v u hu, Complex.ofReal_zero, sub_zero] at hbound
  have havg0 : 0 ≤ realProductAverage (D + 1) w t (maxCoordinateTent ρ) := by
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (Finset.prod_nonneg fun i _ => hw0 (x i)) (maxCoordinateTent_nonneg _ _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg havg0] at hbound
  have hlower := tent_average_lower_bound (D + 1) hρ.le w t hw0 hw i₀ ht
  have hp := hD (D + 1) (by omega)
  nlinarith

theorem exists_dimension_obstruction (M : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∀ a : (Fin d → ℤ) →₀ ℂ, HasTorusBandwidth a M →
      ¬ ∀ β, ‖(maxCoordinateTent (1 / 4) β : ℂ) - torusPolynomial a β‖ ≤ 1 / 16 := by
  obtain ⟨t, ht, b, hb⟩ := exists_real_interpolation_away_from_zero M
  obtain ⟨w, v, hw0, hw, hv0, hv, hwi, hmom⟩ :=
    exists_probability_weights_of_signed_moments M t b hb
  simpa only [show (1 : ℝ) / 4 / 4 = 1 / 16 by norm_num] using
    exists_dimension_obstruction_of_matching_moments (by norm_num : (0 : ℝ) < 1 / 4)
      w (Option.elim' 0 t) v t hw0 hw hv0 hv none hwi rfl ht hmom

theorem exists_continuous_dimension_obstruction (M : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∃ F : C(Fin d → AddCircle (1 : ℝ), ℝ),
      (∀ β, F β ∈ Set.Icc (0 : ℝ) 1) ∧ LipschitzWith 1 F ∧
      ∀ a : (Fin d → ℤ) →₀ ℂ, HasTorusBandwidth a M →
        ¬ ∀ β, ‖(F β : ℂ) - torusPolynomial a β‖ ≤ 1 / 16 := by
  obtain ⟨d, hd, hfail⟩ := exists_dimension_obstruction M
  let F : C(Fin d → AddCircle (1 : ℝ), ℝ) :=
    ⟨maxCoordinateTent (1 / 4), (lipschitzWith_maxCoordinateTent (1 / 4)).continuous⟩
  refine ⟨d, hd, F, ?_, lipschitzWith_maxCoordinateTent _, hfail⟩
  intro β
  exact ⟨maxCoordinateTent_nonneg _ _,
    (maxCoordinateTent_le (by norm_num : (0 : ℝ) ≤ 1 / 4) β).trans (by norm_num)⟩

theorem not_exists_uniform_dimension_bandwidth :
    ¬ ∃ M : ℕ, ∀ d : ℕ, 0 < d →
      ∀ F : C(Fin d → AddCircle (1 : ℝ), ℝ),
        (∀ β, F β ∈ Set.Icc (0 : ℝ) 1) → LipschitzWith 1 F →
        ∃ a : (Fin d → ℤ) →₀ ℂ, HasTorusBandwidth a M ∧
          ∀ β, ‖(F β : ℂ) - torusPolynomial a β‖ ≤ 1 / 16 := by
  rintro ⟨M, hM⟩
  obtain ⟨d, hd, F, hF, hLip, hfail⟩ := exists_continuous_dimension_obstruction M
  obtain ⟨a, ha, happ⟩ := hM d hd F hF hLip
  exact hfail a ha happ

end Sidon.BandwidthCounterexample
