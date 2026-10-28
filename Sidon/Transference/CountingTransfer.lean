module

public import Sidon.Transference.RestrictionBounds
public import Sidon.Analysis.ProductDiscrepancy
public import Sidon.Equidistribution.ProgressionL1

@[expose] public section

/-! # Fourier control of multilinear solution counts -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

private theorem continuous_circle_integrable {f : AddCircle (1 : ℝ) → ℝ}
    (hf : Continuous f) : Integrable f circleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_max_norm_pow_le (F G : C(AddCircle (1 : ℝ), ℂ)) (p : ℕ) {B₁ B₂ : ℝ}
    (hF : (∫ α, ‖F α‖ ^ p ∂circleHaar) ≤ B₁)
    (hG : (∫ α, ‖G α‖ ^ p ∂circleHaar) ≤ B₂) :
    (∫ α, (max ‖F α‖ ‖G α‖) ^ p ∂circleHaar) ≤ B₁ + B₂ := by
  calc
    _ ≤ ∫ α, (‖F α‖ ^ p + ‖G α‖ ^ p) ∂circleHaar := by
      apply integral_mono (continuous_circle_integrable (by fun_prop))
        (continuous_circle_integrable (by fun_prop))
      intro α
      change (max ‖F α‖ ‖G α‖) ^ p ≤ ‖F α‖ ^ p + ‖G α‖ ^ p
      rcases le_total ‖F α‖ ‖G α‖ with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    _ ≤ _ := by
      rw [integral_add (continuous_circle_integrable (by fun_prop))
        (continuous_circle_integrable (by fun_prop))]
      exact add_le_add hF hG

theorem norm_integral_prod_sub_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : 2 ≤ s.card) (F G : ι → C(AddCircle (1 : ℝ), ℂ)) {D B : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ i ∈ s, ∀ α, ‖F i α - G i α‖ ≤ D)
    (hB : ∀ i ∈ s, (∫ α, (max ‖F i α‖ ‖G i α‖) ^ (s.card - 1) ∂circleHaar) ≤ B) :
    ‖∫ α, ((∏ i ∈ s, F i α) - ∏ i ∈ s, G i α) ∂circleHaar‖ ≤ s.card * D * B := by
  have hb (i : ι) (α : AddCircle (1 : ℝ)) : 0 ≤ max ‖F i α‖ ‖G i α‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hp (i : ι) (hi : i ∈ s) :
      (∫ α, ∏ j ∈ s.erase i, max ‖F j α‖ ‖G j α‖ ∂circleHaar) ≤ B := by
    have hcard : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hnonempty : (s.erase i).Nonempty := Finset.card_pos.mp (by omega)
    apply integral_prod_le_of_equal_moments (s.erase i) hnonempty
      (fun j α => max ‖F j α‖ ‖G j α‖) (fun j _ α => hb j α)
      (continuous_circle_integrable (by fun_prop))
      (fun j _ => continuous_circle_integrable (by fun_prop))
    intro j hj
    rw [hcard]
    exact hB j (Finset.mem_of_mem_erase hj)
  calc
    _ ≤ ∫ α, ‖(∏ i ∈ s, F i α) - ∏ i ∈ s, G i α‖ ∂circleHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α, ∑ i ∈ s, D * ∏ j ∈ s.erase i, max ‖F j α‖ ‖G j α‖ ∂circleHaar := by
      apply integral_mono (continuous_circle_integrable (by fun_prop))
        (continuous_circle_integrable (by fun_prop))
      intro α
      apply (norm_prod_sub_prod_le_sum s (fun i => F i α) (fun i => G i α)
        (fun i => max ‖F i α‖ ‖G i α‖) (fun _ _ => le_max_left _ _)
        (fun _ _ => le_max_right _ _)).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hD i hi α) (Finset.prod_nonneg fun j _ => hb j α)
    _ = ∑ i ∈ s, D * ∫ α, ∏ j ∈ s.erase i, max ‖F j α‖ ‖G j α‖ ∂circleHaar := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_const_mul _ _
      · intro i _
        exact continuous_circle_integrable (by fun_prop)
    _ ≤ ∑ _i ∈ s, D * B :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hp i hi) hD0
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem weightedFourier_sub (A : Finset ℤ) (f g : ℤ → ℝ) :
    weightedFourier A (fun n => f n - g n) = weightedFourier A f - weightedFourier A g := by
  ext α
  simp only [weightedFourier_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ContinuousMap.sub_apply]

theorem weightedFourier_zsmul (A : Finset ℤ) (f : ℤ → ℝ) (q : ℤ) (α : AddCircle (1 : ℝ)) :
    weightedFourier A f (q • α) = ∑ n ∈ A, (f n : ℂ) * fourier (q * n) α := by
  rw [weightedFourier_apply]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [fourier_apply, smul_smul, mul_comm]

theorem integral_norm_zsmul_pow_eq (F : C(AddCircle (1 : ℝ), ℂ)) (q : ℤ) (hq : q ≠ 0) (p : ℕ) :
    (∫ α : AddCircle (1 : ℝ), ‖F (q • α)‖ ^ p ∂circleHaar) =
      ∫ α : AddCircle (1 : ℝ), ‖F α‖ ^ p ∂circleHaar := by
  have hmp : MeasurePreserving (fun α : AddCircle (1 : ℝ) => q • α) circleHaar circleHaar :=
    Measure.measurePreserving_zsmul circleHaar hq
  have h := integral_map (μ := circleHaar) hmp.measurable.aemeasurable
    (f := fun α : AddCircle (1 : ℝ) => ‖F α‖ ^ p)
    (F.continuous.norm.pow p).aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

theorem integral_prod_weightedFourier {ι : Type*} [Fintype ι]
    (A : Finset ℤ) (c : ι → ℤ) (f : ι → ℤ → ℝ) :
    (∫ α : AddCircle (1 : ℝ), ∏ i, weightedFourier A (f i) (c i • α) ∂circleHaar) =
      ((weightedSolutionCount A c f : ℝ) : ℂ) := by
  simp_rw [weightedFourier_zsmul]
  rw [integral_prod_expanded_fourier, weightedSolutionCount_ofReal]

theorem norm_weightedFourier_sub_apply_le (A : Finset ℤ) (f g : ℤ → ℝ)
    (α : AddCircle (1 : ℝ)) :
    ‖weightedFourier A f α - weightedFourier A g α‖ ≤
      ‖weightedFourier A (fun n => f n - g n)‖ := by
  rw [weightedFourier_sub]
  exact (weightedFourier A f - weightedFourier A g).norm_coe_le_norm α

def dilateWeightedFourier (A : Finset ℤ) (f : ℤ → ℝ) (q : ℤ) : C(AddCircle (1 : ℝ), ℂ) where
  toFun α := weightedFourier A f (q • α)
  continuous_toFun := by fun_prop

theorem sidon_counting_transfer {N s : ℕ} (hN : 0 < N) (hs : 5 ≤ s)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (c : Fin s → ℤ) (hc : ∀ i, c i ≠ 0)
    (f g : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hfa : ∀ n, f n ≤ (N : ℝ) / S.card)
    (hfs : ∀ n ∈ interval N, n ∉ S → f n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) :
    |weightedSolutionCount (interval N) c (fun _ => f) -
        weightedSolutionCount (interval N) c (fun _ => g)| ≤
      40000 * (s : ℝ) * (N : ℝ) ^ (s - 2) *
        ‖weightedFourier (interval N) (fun n => f n - g n)‖ := by
  classical
  let F : Fin s → C(AddCircle (1 : ℝ), ℂ) := fun i => dilateWeightedFourier (interval N) f (c i)
  let G : Fin s → C(AddCircle (1 : ℝ), ℂ) := fun i => dilateWeightedFourier (interval N) g (c i)
  have hFp (i : Fin s) : (∫ α, ‖F i α‖ ^ (s - 1) ∂circleHaar) ≤
      20000 * (N : ℝ) ^ (s - 2) := by
    change (∫ α, ‖weightedFourier (interval N) f (c i • α)‖ ^ (s - 1) ∂circleHaar) ≤ _
    rw [integral_norm_zsmul_pow_eq _ _ (hc i), ← weightedFourier_mono hSN f hfs]
    have hh := sidon_restriction_moment_le hN (by omega : 4 ≤ s - 1) hS hm f hf0 hfa
    have hexp : (s - 1) - 1 = s - 2 := by omega
    simpa only [hexp] using hh
  have hGp (i : Fin s) : (∫ α, ‖G i α‖ ^ (s - 1) ∂circleHaar) ≤ (N : ℝ) ^ (s - 2) := by
    change (∫ α, ‖weightedFourier (interval N) g (c i • α)‖ ^ (s - 1) ∂circleHaar) ≤ _
    rw [integral_norm_zsmul_pow_eq _ _ (hc i)]
    have hh := interval_restriction_moment_le N (by omega : 2 ≤ s - 1) g hg0 hg1
    have hexp : (s - 1) - 1 = s - 2 := by omega
    simpa only [hexp] using hh
  have hbound := norm_integral_prod_sub_le (Finset.univ : Finset (Fin s))
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega) F G (norm_nonneg _)
    (by intro i _ α; exact norm_weightedFourier_sub_apply_le _ f g (c i • α))
    (B := 40000 * (N : ℝ) ^ (s - 2)) (by
      intro i _
      simp only [Finset.card_univ, Fintype.card_fin]
      have hh := integral_max_norm_pow_le (F i) (G i) (s - 1) (hFp i) (hGp i)
      nlinarith only [hh, pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (s - 2)])
  have heq : (∫ α, ((∏ i, F i α) - ∏ i, G i α) ∂circleHaar) =
      ((weightedSolutionCount (interval N) c (fun _ => f) -
        weightedSolutionCount (interval N) c (fun _ => g) : ℝ) : ℂ) := by
    rw [integral_sub]
    · change (∫ α, ∏ i, weightedFourier (interval N) f (c i • α) ∂circleHaar) -
          (∫ α, ∏ i, weightedFourier (interval N) g (c i • α) ∂circleHaar) = _
      rw [integral_prod_weightedFourier, integral_prod_weightedFourier, Complex.ofReal_sub]
    · exact (show Continuous (fun α : AddCircle (1 : ℝ) => ∏ i, F i α) by
        fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (show Continuous (fun α : AddCircle (1 : ℝ) => ∏ i, G i α) by
        fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [heq, Complex.norm_real, Real.norm_eq_abs, Finset.card_univ, Fintype.card_fin] at hbound
  convert hbound using 1
  ring

end Sidon
