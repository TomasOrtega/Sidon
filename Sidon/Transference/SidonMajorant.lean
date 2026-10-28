module

public import Sidon.Transference.CountingTransfer
public import Sidon.FourierUniformity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! # The normalized Sidon majorant used in transference -/

noncomputable section

namespace Sidon

def sidonMajorant (N : ℕ) (S : Finset ℤ) (n : ℤ) : ℝ :=
  if n ∈ S then (N : ℝ) / S.card else 0

theorem sidonMajorant_nonneg (N : ℕ) (S : Finset ℤ) (n : ℤ) : 0 ≤ sidonMajorant N S n := by
  unfold sidonMajorant
  split_ifs <;> positivity

theorem sidonMajorant_le (N : ℕ) (S : Finset ℤ) (n : ℤ) :
    sidonMajorant N S n ≤ (N : ℝ) / S.card := by
  unfold sidonMajorant
  split_ifs
  · exact le_rfl
  · positivity

theorem sidonMajorant_eq_zero (N : ℕ) {S : Finset ℤ} {n : ℤ} (hn : n ∉ S) :
    sidonMajorant N S n = 0 := if_neg hn

theorem sum_sidonMajorant {N : ℕ} {S : Finset ℤ} (hm : 0 < S.card)
    (hSN : S ⊆ interval N) : (∑ n ∈ interval N, sidonMajorant N S n) = N := by
  have hm0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Finset.sum_subset hSN (fun n _ hn => sidonMajorant_eq_zero N hn)]
  calc
    _ = ∑ _n ∈ S, (N : ℝ) / S.card :=
      Finset.sum_congr rfl fun n hn => if_pos hn
    _ = N := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

theorem weightedFinsupp_sidonMajorant {N : ℕ} {S : Finset ℤ} (hSN : S ⊆ interval N) :
    weightedFinsupp (interval N) (sidonMajorant N S) =
      ((N : ℝ) / S.card) • indicatorFinsupp S := by
  ext n
  by_cases hns : n ∈ S
  · simp only [weightedFinsupp, Finsupp.indicator_of_mem (hSN hns), sidonMajorant, if_pos hns,
      Finsupp.smul_apply, indicatorFinsupp_apply, Complex.real_smul, Complex.ofReal_one, mul_one]
  · by_cases hn : n ∈ interval N
    · simp only [weightedFinsupp, Finsupp.indicator_of_mem hn, sidonMajorant, if_neg hns,
        Complex.ofReal_zero, Finsupp.smul_apply, indicatorFinsupp_apply, smul_zero]
    · simp only [weightedFinsupp, Finsupp.indicator_of_notMem hn, Finsupp.smul_apply,
        indicatorFinsupp_apply, if_neg hns, smul_zero]

theorem weightedFourier_sidonMajorant_sub_one {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hm : 0 < S.card) (hSN : S ⊆ interval N) :
    weightedFourier (interval N) (fun n => sidonMajorant N S n - 1) =
      ((N : ℝ) / S.card) • fourierSum (discrepancyFunction N S) := by
  rw [weightedFourier_sub, ← fourierSum_weightedFinsupp, weightedFinsupp_sidonMajorant hSN,
    fourierSum_real_smul, weightedFourier_one, fourierSum_discrepancyFunction,
    smul_sub, smul_smul]
  have heq : ((N : ℝ) / S.card) * ((S.card : ℝ) / N) = 1 := by
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hm0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [heq, one_smul]

theorem sqrt_half_le_card_of_deviation_le_half {N : ℕ} (hN : 0 < N) (S : Finset ℤ)
    (hdev : sidonDeviation N S ≤ 1 / 2) : Real.sqrt N / 2 ≤ S.card := by
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hlow : (1 / 2 : ℝ) ≤ (S.card : ℝ) / Real.sqrt N := by
    have hh := (abs_le.mp hdev).1
    linarith
  have hh := (le_div_iff₀ hroot).mp hlow
  linarith

theorem sidonMajorant_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 2 ≤ S.card) :
    ‖weightedFourier (interval N) (fun n => sidonMajorant N S n - 1)‖ ≤
      32 * (N : ℝ) * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 2).trans_le hm
  have hmnat : 0 < S.card := by exact_mod_cast hmpos
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [weightedFourier_sidonMajorant_sub_one hN hmnat hSN,
    norm_smul ((N : ℝ) / S.card) (fourierSum (discrepancyFunction N S)),
    Real.norm_eq_abs, abs_of_pos (div_pos hNpos hmpos)]
  have hb := sidon_fourier_uniformity hN hS hSN
  rw [← fourierSum_discrepancyFunction] at hb
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg hNpos.le hmpos.le)).trans
  have hratio : Real.sqrt (N : ℝ) / S.card ≤ 2 := (div_le_iff₀ hmpos).mpr (by linarith)
  have hscale : ((N : ℝ) / S.card) * (16 * Real.sqrt N) ≤ 32 * N := by
    calc
      _ = (16 * (N : ℝ)) * (Real.sqrt N / S.card) := by ring
      _ ≤ (16 * (N : ℝ)) * 2 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  calc
    _ = (((N : ℝ) / S.card) * (16 * Real.sqrt N)) *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg _)

theorem exists_sidon_uniformity_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℤ, sidonDeviation N S ≤ γ →
        32 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ≤ η := by
  have hlimit : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 6 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ (-(1 / 6 : ℝ)) < η ^ 2 / 4096 :=
    hlimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η ^ 2 / 4096))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hsmall
  let γ := min (1 / 2 : ℝ) (η ^ 2 / 4096)
  refine ⟨max M 1, le_max_right _ _, γ, by dsimp [γ]; positivity, min_le_left _ _, ?_⟩
  intro N hN S hdev
  have hpow := hM N ((le_max_left M 1).trans hN)
  have hdev' := hdev.trans (min_le_right (1 / 2 : ℝ) (η ^ 2 / 4096))
  have hE : 0 ≤ sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
    unfold sidonDeviation
    positivity
  have hroot : Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ≤ η / 32 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  nlinarith

end Sidon
