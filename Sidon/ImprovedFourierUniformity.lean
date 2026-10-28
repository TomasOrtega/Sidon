module

public import Sidon.Cilleruelo
public import Sidon.FourierUniformity

@[expose] public section

/-! # The quarter-power improvement to Fourier uniformity -/

noncomputable section

namespace Sidon

theorem boundaryPart_card_le_cilleruelo {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (h : ℤ)
    (hhN : |h| ≤ (N : ℤ)) (hhP : |(h : ℝ)| ≤ (N : ℝ) ^ (3 / 4 : ℝ)) :
    ((boundaryPart N S h).card : ℝ) ≤
      37 * ((N : ℝ) ^ (1 / 4 : ℝ) +
        Real.sqrt (sidonDeviation N S) * (N : ℝ) ^ (3 / 8 : ℝ)) := by
  have habs : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hL : (h.natAbs : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by rwa [habs]
  have hh' := abs_le.mp hhN
  by_cases hh : 0 ≤ h
  · have hnat : (h.natAbs : ℤ) = h := by rw [Int.natCast_natAbs, abs_of_nonneg hh]
    have hsub : boundaryPart N S h ⊆ S ∩
        Finset.Icc ((N : ℤ) - h + 1) ((N : ℤ) - h + h.natAbs) := by
      intro x hx
      obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
      have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
      exact Finset.mem_inter.mpr ⟨hxS, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    apply (show ((boundaryPart N S h).card : ℝ) ≤
      ((S ∩ Finset.Icc ((N : ℤ) - h + 1) ((N : ℤ) - h + h.natAbs)).card : ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans
    simpa only [sidonDeviation, abs_sub_comm] using
      cilleruelo_short_interval hN hS hSN ((N : ℤ) - h) (by omega) (by omega) hL
  · have hnat : (h.natAbs : ℤ) = -h := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hh)]
    have hsub : boundaryPart N S h ⊆ S ∩ Finset.Icc 1 (h.natAbs : ℤ) := by
      intro x hx
      obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
      have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
      exact Finset.mem_inter.mpr ⟨hxS, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    apply (show ((boundaryPart N S h).card : ℝ) ≤
      ((S ∩ Finset.Icc 1 (h.natAbs : ℤ)).card : ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans
    simpa only [zero_add, sidonDeviation, abs_sub_comm] using
      cilleruelo_short_interval hN hS hSN 0 (by omega) (by omega) hL

theorem improved_mixed_correlationError_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hHN : H ≤ N) (hHP : (H : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ)) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    correlationError N S H (indicatorFinsupp S) (intervalModel N S) ≤
      37 * (S.card : ℝ) / N * ((N : ℝ) ^ (1 / 4 : ℝ) +
        Real.sqrt (sidonDeviation N S) * (N : ℝ) ^ (3 / 8 : ℝ)) := by
  unfold correlationError
  apply sum_fejerWeight_mul_le H hH
  intro h hh
  rw [intervalModel_mixed_deficit]
  have habs : |h| ≤ (N : ℤ) :=
    (abs_lt_of_mem_support_fejerWeight H hh).le.trans (by exact_mod_cast hHN)
  have habs' : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (abs_lt_of_mem_support_fejerWeight H hh).le
  have hbound := boundaryPart_card_le_cilleruelo hN hS hSN h habs (habs'.trans hHP)
  calc
    ((S.card : ℝ) / N) * (boundaryPart N S h).card ≤
        ((S.card : ℝ) / N) * (37 * ((N : ℝ) ^ (1 / 4 : ℝ) +
          Real.sqrt (sidonDeviation N S) * (N : ℝ) ^ (3 / 8 : ℝ))) := by gcongr
    _ = _ := by ring

theorem improved_fourier_error_master_le {N H m E₁₁ E₂₂ E₁₂ E₂₁ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hHN : H ≤ N) (hm₀ : 0 ≤ m)
    (hm : m ≤ 5 * Real.sqrt N)
    (h₁₁ : E₁₁ ≤ 2 * |m ^ 2 / N - 1| + m ^ 2 * H / N ^ 2 + 2 * m / H)
    (h₂₂ : E₂₂ ≤ m ^ 2 * H / N ^ 2)
    (h₁₂ : E₁₂ ≤ 37 * m / N *
      (N ^ (1 / 4 : ℝ) + Real.sqrt |m / Real.sqrt N - 1| * N ^ (3 / 8 : ℝ)))
    (h₂₁ : E₂₁ ≤ 37 * m / N *
      (N ^ (1 / 4 : ℝ) + Real.sqrt |m / Real.sqrt N - 1| * N ^ (3 / 8 : ℝ))) :
    (N + H) * (E₁₁ + E₂₂ + E₁₂ + E₂₁) ≤
      24 * N * |m / Real.sqrt N - 1| + 100 * H + 20 * N * Real.sqrt N / H +
        740 * N ^ (3 / 4 : ℝ) + 740 * Real.sqrt |m / Real.sqrt N - 1| * N ^ (7 / 8 : ℝ) := by
  let B := N ^ (1 / 4 : ℝ) + Real.sqrt |m / Real.sqrt N - 1| * N ^ (3 / 8 : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hdev := normalized_square_deviation_le hN hm₀ hm
  have hmSq : m ^ 2 ≤ 25 * N := by nlinarith [Real.sq_sqrt hN.le]
  have hterm : m ^ 2 * H / N ^ 2 ≤ 25 * H / N := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmSq (mul_nonneg hH.le hN.le)]
  have htermH : 2 * m / H ≤ 10 * Real.sqrt N / H :=
    div_le_div_of_nonneg_right (by linarith) hH.le
  have hmix : 37 * m / N * B ≤ 185 * Real.sqrt N / N * B :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by nlinarith [hm]) hN.le) hB
  have hsum : E₁₁ + E₂₂ + E₁₂ + E₂₁ ≤
      12 * |m / Real.sqrt N - 1| + 50 * H / N + 10 * Real.sqrt N / H +
        370 * Real.sqrt N / N * B := by
    change E₁₂ ≤ 37 * m / N * B at h₁₂
    change E₂₁ ≤ 37 * m / N * B at h₂₁
    ring_nf at h₁₁ h₂₂ h₁₂ h₂₁ hdev hterm htermH hmix ⊢
    linarith only [h₁₁, h₂₂, h₁₂, h₂₁, hdev, hterm, htermH, hmix]
  have hsum₀ : 0 ≤ 12 * |m / Real.sqrt N - 1| + 50 * H / N +
      10 * Real.sqrt N / H + 370 * Real.sqrt N / N * B := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ N + H)
  have hscaled' := mul_le_mul_of_nonneg_right (by linarith : N + H ≤ 2 * N) hsum₀
  have hidentity : 2 * N * (12 * |m / Real.sqrt N - 1| + 50 * H / N +
      10 * Real.sqrt N / H + 370 * Real.sqrt N / N * B) =
      24 * N * |m / Real.sqrt N - 1| + 100 * H +
        20 * N * Real.sqrt N / H + 740 * Real.sqrt N * B := by
    field_simp [ne_of_gt hN, ne_of_gt hH]
    ring
  have hp25 : Real.sqrt N * N ^ (1 / 4 : ℝ) = N ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  have hp38 : Real.sqrt N * N ^ (3 / 8 : ℝ) = N ^ (7 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  have hBroot : Real.sqrt N * B = N ^ (3 / 4 : ℝ) +
      Real.sqrt |m / Real.sqrt N - 1| * N ^ (7 / 8 : ℝ) := by
    calc
      _ = Real.sqrt N * N ^ (1 / 4 : ℝ) +
          Real.sqrt |m / Real.sqrt N - 1| * (Real.sqrt N * N ^ (3 / 8 : ℝ)) := by
        dsimp only [B]
        ring
      _ = _ := by rw [hp25, hp38]
  rw [hidentity, mul_assoc 740, hBroot] at hscaled'
  nlinarith only [hscaled, hscaled']

theorem improved_diagonal_window_error_le {N H : ℝ} (hN : 0 < N)
    (hH : N ^ (3 / 4 : ℝ) / 2 ≤ H) :
    N * Real.sqrt N / H ≤ 2 * N ^ (3 / 4 : ℝ) := by
  have hp : 0 < N ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
  have heq : N * Real.sqrt N / N ^ (3 / 4 : ℝ) = N ^ (3 / 4 : ℝ) := by
    calc
      N * Real.sqrt N / N ^ (3 / 4 : ℝ) =
          N ^ ((1 : ℝ) + 1 / 2) / N ^ (3 / 4 : ℝ) := by
        rw [Real.rpow_add hN, Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ = N ^ ((1 : ℝ) + 1 / 2 - 3 / 4) := (Real.rpow_sub hN _ _).symm
      _ = _ := by norm_num
  calc
    N * Real.sqrt N / H ≤ N * Real.sqrt N / (N ^ (3 / 4 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hH
    _ = 2 * (N * Real.sqrt N / N ^ (3 / 4 : ℝ)) := by ring
    _ = _ := by rw [heq]

theorem mixed_deviation_amgm {N δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ) :
    2 * Real.sqrt δ * N ^ (7 / 8 : ℝ) ≤ N * δ + N ^ (3 / 4 : ℝ) := by
  have hp38 : Real.sqrt N * N ^ (3 / 8 : ℝ) = N ^ (7 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  have hpow : (N ^ (3 / 8 : ℝ)) ^ 2 = N ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  calc
    2 * Real.sqrt δ * N ^ (7 / 8 : ℝ) =
        2 * (Real.sqrt N * Real.sqrt δ) * N ^ (3 / 8 : ℝ) := by rw [← hp38]; ring
    _ ≤ (Real.sqrt N * Real.sqrt δ) ^ 2 + (N ^ (3 / 8 : ℝ)) ^ 2 := two_mul_le_add_sq _ _
    _ = _ := by rw [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hδ, hpow]

theorem sidon_improved_fourier_discrepancy_sq_le {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤
      1250 * N * (sidonDeviation N S + (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let H := ⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊
  have hw := floor_rpow_window_spec hN (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hH : 0 < H := hw.1
  have hHN : H ≤ N := hw.2.1
  have hNr : (0 : ℝ) < N := by positivity
  have hHr : (0 : ℝ) < H := by positivity
  have hmixed := improved_mixed_correlationError_le hN hH hHN hw.2.2.2 hS hSN
  have hmixed' : correlationError N S H (intervalModel N S) (indicatorFinsupp S) ≤
      37 * (S.card : ℝ) / N * ((N : ℝ) ^ (1 / 4 : ℝ) +
        Real.sqrt (sidonDeviation N S) * (N : ℝ) ^ (3 / 8 : ℝ)) := by
    rw [correlationError_swap]
    exact hmixed
  have hmaster := improved_fourier_error_master_le hNr hHr
    (show (H : ℝ) ≤ N by exact_mod_cast hHN) (Nat.cast_nonneg S.card)
    (hS.card_le_five_mul_sqrt hSN) (self_correlationError_le hN hH hS hSN)
    (intervalModel_correlationError_le hN hH hHN S) hmixed hmixed'
  have hbound := (discrepancy_fourier_sq_le_errors hH hSN α).trans hmaster
  have hdiag := improved_diagonal_window_error_le hNr hw.2.2.1
  have hwindow := hw.2.2.2
  have hamgm := mixed_deviation_amgm hNr (abs_nonneg ((S.card : ℝ) / Real.sqrt N - 1))
  have hδterm : 0 ≤ (N : ℝ) * sidonDeviation N S := by unfold sidonDeviation; positivity
  have hsq : ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤
      1250 * (N : ℝ) * sidonDeviation N S + 1250 * (N : ℝ) ^ (3 / 4 : ℝ) := by
    change ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤
      1250 * (N : ℝ) * |(S.card : ℝ) / Real.sqrt N - 1| +
        1250 * (N : ℝ) ^ (3 / 4 : ℝ)
    change 0 ≤ (N : ℝ) * |(S.card : ℝ) / Real.sqrt N - 1| at hδterm
    ring_nf at hbound hdiag hamgm hwindow hδterm ⊢
    linarith only [hbound, hdiag, hamgm, hwindow, hδterm]
  have hpower : (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) ^ ((1 : ℝ) + -(1 / 4 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hNr, Real.rpow_one]
  rw [hpower] at hsq
  nlinarith only [hsq]

/-- Theorem 6.3, including the finite-window proof of its interval input. -/
theorem sidon_improved_fourier_uniformity_apply {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (discrepancyFunction N S) α‖ ≤
      36 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let E : ℝ := sidonDeviation N S + (N : ℝ) ^ (-(1 / 4 : ℝ))
  have hE : 0 ≤ E := by unfold E sidonDeviation; positivity
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hbound := sidon_improved_fourier_discrepancy_sq_le hN hS hSN α
  change ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤ 1250 * (N : ℝ) * E at hbound
  have hsq : (36 * Real.sqrt N * Real.sqrt E) ^ 2 = 1296 * (N : ℝ) * E := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hNr, Real.sq_sqrt hE]
    norm_num
  have htarget : 0 ≤ 36 * Real.sqrt N * Real.sqrt E := by positivity
  have hle : ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤
      (36 * Real.sqrt N * Real.sqrt E) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg hNr hE]
  simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg htarget] using sq_le_sq.mp hle

theorem sidon_improved_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    ‖fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
      36 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
  rw [← fourierSum_discrepancyFunction]
  exact (ContinuousMap.norm_le (fourierSum (discrepancyFunction N S)) (by positivity)).mpr
    (sidon_improved_fourier_uniformity_apply hN hS hSN)

end Sidon
