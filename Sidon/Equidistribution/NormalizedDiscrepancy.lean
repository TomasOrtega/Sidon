module

public import Sidon.FourierUniformity
public import Sidon.Equidistribution.TorusSmoothing
public import Mathlib.Algebra.BigOperators.Expect

@[expose] public section

/-! # Normalized discrepancy and finite orbit averages -/

noncomputable section

namespace Sidon

/-- Difference between the two normalized counting measures. -/
def normalizedDiscrepancy (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  (S.card : ℝ)⁻¹ • indicatorFinsupp S - (N : ℝ)⁻¹ • indicatorFinsupp (interval N)

theorem support_normalizedDiscrepancy {N : ℕ} {S : Finset ℤ} (hSN : S ⊆ interval N) :
    (normalizedDiscrepancy N S).support ⊆ interval N := by
  intro x hx
  by_contra hxn
  have hxs : x ∉ S := fun h => hxn (hSN h)
  have hz : normalizedDiscrepancy N S x = 0 := by
    simp [normalizedDiscrepancy, indicatorFinsupp_apply, hxs, hxn]
  exact (Finsupp.mem_support_iff.mp hx) hz

theorem sum_norm_indicatorFinsupp_of_subset (S T : Finset ℤ) (hST : S ⊆ T) :
    (∑ x ∈ T, ‖indicatorFinsupp S x‖) = (S.card : ℝ) := by
  rw [← Finset.sum_subset hST (fun x _ hx => by simp [indicatorFinsupp_apply, hx])]
  calc
    ∑ x ∈ S, ‖indicatorFinsupp S x‖ = ∑ _x ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [indicatorFinsupp_apply, if_pos hx, norm_one]
    _ = _ := by simp

theorem sum_norm_normalizedDiscrepancy_le_two {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hm : 0 < S.card) (hSN : S ⊆ interval N) :
    (normalizedDiscrepancy N S).sum (fun _ c => ‖c‖) ≤ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < S.card := by exact_mod_cast hm
  rw [Finsupp.sum_of_support_subset _ (support_normalizedDiscrepancy hSN)
    (fun _ c => ‖c‖) (fun _ _ => norm_zero)]
  calc
    (∑ x ∈ interval N, ‖normalizedDiscrepancy N S x‖) ≤
        ∑ x ∈ interval N, ((S.card : ℝ)⁻¹ * ‖indicatorFinsupp S x‖ +
          (N : ℝ)⁻¹ * ‖indicatorFinsupp (interval N) x‖) := by
      apply Finset.sum_le_sum
      intro x _
      apply (norm_sub_le _ _).trans_eq
      rw [Finsupp.smul_apply, Finsupp.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hmpos), abs_of_pos (inv_pos.mpr hNpos)]
    _ = 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_norm_indicatorFinsupp_of_subset S (interval N) hSN,
        sum_norm_indicatorFinsupp_of_subset (interval N) (interval N) Finset.Subset.rfl,
        card_interval, inv_mul_cancel₀ hmpos.ne', inv_mul_cancel₀ hNpos.ne']
      norm_num

theorem normalizedDiscrepancy_eq_smul_discrepancyFunction {N : ℕ} {S : Finset ℤ}
    (hm : 0 < S.card) :
    normalizedDiscrepancy N S = (S.card : ℝ)⁻¹ • discrepancyFunction N S := by
  unfold normalizedDiscrepancy discrepancyFunction intervalModel
  rw [smul_sub, smul_smul]
  have heq : (S.card : ℝ)⁻¹ * ((S.card : ℝ) / N) = (N : ℝ)⁻¹ := by
    have hm0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [heq]

theorem torusTest_sub {d : ℕ} (f g : ℤ →₀ ℂ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest (f - g) F α = torusTest f F α - torusTest g F α := by
  exact Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

theorem torusTest_real_smul {d : ℕ} (c : ℝ) (f : ℤ →₀ ℂ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest (c • f) F α = c • torusTest f F α := by
  unfold torusTest
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Complex.real_smul, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem torusTest_indicatorFinsupp {d : ℕ} (S : Finset ℤ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest (indicatorFinsupp S) F α = ∑ x ∈ S, F (x • α) := by
  rw [torusTest, Finsupp.sum, support_indicatorFinsupp]
  apply Finset.sum_congr rfl
  intro x hx
  rw [indicatorFinsupp_apply, if_pos hx, one_mul]

theorem torusTest_normalizedDiscrepancy {d : ℕ} (N : ℕ) (S : Finset ℤ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest (normalizedDiscrepancy N S) F α =
      Finset.expect S (fun x => F (x • α)) -
        Finset.expect (interval N) (fun x => F (x • α)) := by
  rw [normalizedDiscrepancy, torusTest_sub, torusTest_real_smul, torusTest_real_smul,
    torusTest_indicatorFinsupp, torusTest_indicatorFinsupp,
    Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, card_interval]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
  ring

theorem torusTest_normalizedDiscrepancy_complexify {d : ℕ} (N : ℕ) (S : Finset ℤ)
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest (normalizedDiscrepancy N S) (torusComplexify F) α =
      ((Finset.expect S (fun x => F (x • α)) -
        Finset.expect (interval N) (fun x => F (x • α)) : ℝ) : ℂ) := by
  rw [torusTest_normalizedDiscrepancy]
  simp only [Finset.expect_eq_sum_div_card, torusComplexify_apply, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

theorem sidon_normalized_fourier_uniformity_apply {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (normalizedDiscrepancy N S) α‖ ≤
      1600 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  have hmnat : 0 < S.card := by exact_mod_cast hmpos
  rw [normalizedDiscrepancy_eq_smul_discrepancyFunction hmnat, fourierSum_real_smul,
    ContinuousMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmpos)]
  apply (mul_le_mul_of_nonneg_left (sidon_fourier_uniformity_apply hN hS hSN α)
    (inv_nonneg.mpr hmpos.le)).trans
  have hratio : (S.card : ℝ)⁻¹ * (16 * Real.sqrt N) ≤ 1600 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [hm]
  calc
    (S.card : ℝ)⁻¹ *
        (16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)))) =
      ((S.card : ℝ)⁻¹ * (16 * Real.sqrt N)) *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)

theorem sidon_normalized_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) :
    ‖fourierSum (normalizedDiscrepancy N S)‖ ≤
      1600 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) :=
  (ContinuousMap.norm_le _ (by positivity)).mpr
    (sidon_normalized_fourier_uniformity_apply hN hS hSN hm)

end Sidon
