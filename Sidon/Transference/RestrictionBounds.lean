import Sidon.Transference.RestrictionMoments

/-! # Restriction bounds for Sidon and bounded interval functions -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

def weightedFinsupp (A : Finset ℤ) (f : ℤ → ℝ) : ℤ →₀ ℂ :=
  Finsupp.indicator A fun n _ => (f n : ℂ)

theorem support_weightedFinsupp (A : Finset ℤ) (f : ℤ → ℝ) :
    (weightedFinsupp A f).support ⊆ A := Finsupp.support_indicator_subset _ _

theorem fourierSum_weightedFinsupp (A : Finset ℤ) (f : ℤ → ℝ) :
    fourierSum (weightedFinsupp A f) = weightedFourier A f := by
  rw [fourierSum, Finsupp.sum_of_support_subset _ (support_weightedFinsupp A f)
    (fun (n : ℤ) (c : ℂ) => c • (fourier n : C(AddCircle (1 : ℝ), ℂ)))
    (fun n _ => zero_smul ℂ (fourier (T := 1) n))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weightedFinsupp, Finsupp.indicator_of_mem hn]

theorem integral_norm_weightedFourier_sq (A : Finset ℤ) (f : ℤ → ℝ) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier A f α‖ ^ 2 ∂circleHaar) =
      ∑ n ∈ A, (f n) ^ 2 := by
  rw [← fourierSum_weightedFinsupp, integral_norm_fourierSum_sq,
    Finsupp.sum_of_support_subset _ (support_weightedFinsupp A f)
      (fun _ c => ‖c‖ ^ 2) (fun _ _ => by simp)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weightedFinsupp, Finsupp.indicator_of_mem hn, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem weightedFourier_mono {S T : Finset ℤ} (hST : S ⊆ T) (f : ℤ → ℝ)
    (hf : ∀ n ∈ T, n ∉ S → f n = 0) : weightedFourier S f = weightedFourier T f := by
  unfold weightedFourier
  exact Finset.sum_subset hST (fun n hn hns => by simp only [hf n hn hns, Complex.ofReal_zero,
    zero_smul ℂ (fourier (T := 1) n)])

theorem norm_pow_le_of_le {x M : ℝ} (hx : 0 ≤ x) (hM : x ≤ M) {p k : ℕ} (hkp : k ≤ p) :
    x ^ p ≤ M ^ (p - k) * x ^ k := by
  calc
    x ^ p = x ^ (p - k) * x ^ k := by rw [← pow_add, Nat.sub_add_cancel hkp]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left hx hM _) (pow_nonneg hx _)

theorem integral_norm_weightedFourier_pow_le {p k : ℕ} (hkp : k ≤ p)
    (A : Finset ℤ) (f : ℤ → ℝ) {M B : ℝ} (hM : 0 ≤ M)
    (hF : ∀ α, ‖weightedFourier A f α‖ ≤ M)
    (hB : (∫ α : AddCircle (1 : ℝ), ‖weightedFourier A f α‖ ^ k ∂circleHaar) ≤ B) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier A f α‖ ^ p ∂circleHaar) ≤ M ^ (p - k) * B := by
  have hint (j : ℕ) : Integrable
      (fun α : AddCircle (1 : ℝ) => ‖weightedFourier A f α‖ ^ j) circleHaar :=
    (show Continuous (fun α : AddCircle (1 : ℝ) => ‖weightedFourier A f α‖ ^ j) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ α : AddCircle (1 : ℝ), M ^ (p - k) * ‖weightedFourier A f α‖ ^ k ∂circleHaar := by
      apply integral_mono (hint p) ((hint k).const_mul _)
      intro α
      exact norm_pow_le_of_le (norm_nonneg _) (hF α) hkp
    _ = M ^ (p - k) * ∫ α : AddCircle (1 : ℝ), ‖weightedFourier A f α‖ ^ k ∂circleHaar :=
      integral_mul_left _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (pow_nonneg hM _)

theorem sidon_weighted_fourth_moment_le {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hm : Real.sqrt N / 100 ≤ S.card)
    (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hfa : ∀ n, f n ≤ (N : ℝ) / S.card) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier S f α‖ ^ 4 ∂circleHaar) ≤
      20000 * (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  have hfour := integral_norm_weightedFourier_fourth_le hS f hf0 hfa
  have heq : ((N : ℝ) / S.card) ^ 4 * (2 * (S.card : ℝ) ^ 2) =
      2 * (N : ℝ) ^ 4 / (S.card : ℝ) ^ 2 := by field_simp; ring
  rw [heq] at hfour
  have hm2 : (N : ℝ) ≤ 10000 * (S.card : ℝ) ^ 2 := by
    have hsqrt := Real.sq_sqrt hNpos.le
    have hscaled : Real.sqrt N ≤ 100 * (S.card : ℝ) := by linarith
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg (N : ℝ)) hscaled
    nlinarith only [hsquare, hsqrt]
  apply hfour.trans
  apply (div_le_iff₀ (sq_pos_of_pos hmpos)).mpr
  have hh := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 2 * (N : ℝ) ^ 3)
  nlinarith only [hh]

theorem norm_weightedFourier_sidon_majorant_le {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hm : Real.sqrt N / 100 ≤ S.card) (f : ℤ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hfa : ∀ n, f n ≤ (N : ℝ) / S.card)
    (α : AddCircle (1 : ℝ)) : ‖weightedFourier S f α‖ ≤ N := by
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  calc
    _ ≤ ∑ n ∈ S, |f n| := norm_weightedFourier_apply_le S f α
    _ = ∑ n ∈ S, f n := Finset.sum_congr rfl fun n _ => abs_of_nonneg (hf0 n)
    _ ≤ ∑ _n ∈ S, (N : ℝ) / S.card := Finset.sum_le_sum fun n _ => hfa n
    _ = N := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

theorem sidon_restriction_moment_le {N p : ℕ} (hN : 0 < N) (hp : 4 ≤ p)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hm : Real.sqrt N / 100 ≤ S.card)
    (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hfa : ∀ n, f n ≤ (N : ℝ) / S.card) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier S f α‖ ^ p ∂circleHaar) ≤
      20000 * (N : ℝ) ^ (p - 1) := by
  have h := integral_norm_weightedFourier_pow_le hp S f (Nat.cast_nonneg N)
    (norm_weightedFourier_sidon_majorant_le hN hm f hf0 hfa)
    (sidon_weighted_fourth_moment_le hN hS hm f hf0 hfa)
  have hexp : (p - 4) + 3 = p - 1 := by omega
  calc
    _ ≤ (N : ℝ) ^ (p - 4) * (20000 * (N : ℝ) ^ 3) := h
    _ = _ := by rw [← mul_assoc, mul_comm ((N : ℝ) ^ (p - 4)) 20000, mul_assoc,
      ← pow_add, hexp]

theorem norm_weightedFourier_interval_le (N : ℕ) (g : ℤ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) (α : AddCircle (1 : ℝ)) :
    ‖weightedFourier (interval N) g α‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ interval N, |g n| := norm_weightedFourier_apply_le _ _ _
    _ = ∑ n ∈ interval N, g n := Finset.sum_congr rfl fun n _ => abs_of_nonneg (hg0 n)
    _ ≤ ∑ _n ∈ interval N, (1 : ℝ) := Finset.sum_le_sum fun n _ => hg1 n
    _ = N := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_interval]

theorem interval_weighted_second_moment_le (N : ℕ) (g : ℤ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier (interval N) g α‖ ^ 2 ∂circleHaar) ≤ N := by
  rw [integral_norm_weightedFourier_sq]
  calc
    _ ≤ ∑ _n ∈ interval N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [one_pow] using pow_le_pow_left (hg0 n) (hg1 n) 2
    _ = N := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_interval]

theorem interval_restriction_moment_le {p : ℕ} (N : ℕ) (hp : 2 ≤ p)
    (g : ℤ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) :
    (∫ α : AddCircle (1 : ℝ), ‖weightedFourier (interval N) g α‖ ^ p ∂circleHaar) ≤
      (N : ℝ) ^ (p - 1) := by
  have h := integral_norm_weightedFourier_pow_le hp (interval N) g (Nat.cast_nonneg N)
    (norm_weightedFourier_interval_le N g hg0 hg1) (interval_weighted_second_moment_le N g hg0 hg1)
  have hexp : (p - 2) + 1 = p - 1 := by omega
  calc
    _ ≤ (N : ℝ) ^ (p - 2) * N := h
    _ = _ := by rw [← pow_succ, hexp]

end Sidon
