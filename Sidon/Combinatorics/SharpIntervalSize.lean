import Sidon.Analysis.SidonCorrelation
import Sidon.Analysis.PowerWindow

/-! # The square-root Sidon bound with a quarter-power error -/

namespace Sidon

theorem weighted_indicator_self_correlation_le {H : ℕ} (hH : 0 < H)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) :
    (fejerWeight H).sum (fun h w =>
      w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) ≤
      1 + (S.card : ℝ) / H := by
  have hzero : 0 ∈ (fejerWeight H).support := by
    rw [Finsupp.mem_support_iff, fejerWeight_zero H hH]
    positivity
  have hdelta : (fejerWeight H).sum
      (fun h w => w * (if h = 0 then (S.card : ℝ) else 0)) = (S.card : ℝ) / H := by
    simp only [mul_ite, mul_zero, Finsupp.sum]
    rw [Finset.sum_ite_eq']
    simp only [hzero, if_true, fejerWeight_zero H hH]
    ring
  calc
    (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) ≤
        (fejerWeight H).sum (fun h w =>
          w * (1 + if h = 0 then (S.card : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro h _
      apply mul_le_mul_of_nonneg_left _ (fejerWeight_nonneg H h)
      by_cases hh : h = 0
      · subst h
        rw [re_correlation_indicatorFinsupp_zero, if_pos rfl]
        linarith
      · rw [if_neg hh, add_zero]
        exact re_correlation_indicatorFinsupp_le_one hS hh
    _ = (fejerWeight H).sum (fun _ w => w) +
        (fejerWeight H).sum
          (fun h w => w * (if h = 0 then (S.card : ℝ) else 0)) := by
      simp only [Finsupp.sum, mul_add, mul_one, Finset.sum_add_distrib]
    _ = _ := by rw [sum_fejerWeight H hH, hdelta]

theorem sidon_card_sq_le_window {N H : ℕ} (hH : 0 < H) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    (S.card : ℝ) ^ 2 ≤ ((N : ℝ) + H) * ((S.card : ℝ) / H + 1) := by
  have hmass := self_correlation_mass_ge hH S hSN
  have hupper := weighted_indicator_self_correlation_le hH hS
  have hden : (0 : ℝ) < (N : ℝ) + H := by positivity
  have hbound := (div_le_iff₀ hden).mp (hmass.trans hupper)
  simpa only [add_comm, mul_comm] using hbound

theorem sqrt_add_le_sqrt_add_div_sqrt {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H) :
    Real.sqrt (N + H) ≤ Real.sqrt N + H / Real.sqrt N := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsN := Real.sq_sqrt hN.le
  have hsNH := Real.sq_sqrt (by linarith : 0 ≤ N + H)
  have hdiv : H / Real.sqrt N * Real.sqrt N = H := div_mul_cancel₀ H (ne_of_gt hs)
  have hdiv₀ : 0 ≤ H / Real.sqrt N := div_nonneg hH hs.le
  have hsNH₀ := Real.sqrt_nonneg (N + H)
  nlinarith [sq_nonneg (H / Real.sqrt N)]

theorem sidon_card_le_window {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    (S.card : ℝ) ≤ Real.sqrt N + (H : ℝ) / Real.sqrt N + (N : ℝ) / H + 1 := by
  have hquad := sidon_card_sq_le_window hH hS hSN
  have hquad' : (S.card : ℝ) ^ 2 ≤
      (((N : ℝ) + H) / H) * (S.card : ℝ) + ((N : ℝ) + H) := by
    nlinarith [show ((N : ℝ) + H) * ((S.card : ℝ) / H + 1) =
      (((N : ℝ) + H) / H) * (S.card : ℝ) + ((N : ℝ) + H) by ring]
  have hbound := le_add_sqrt_of_sq_le (by positivity) (by positivity) hquad'
  have hroot := sqrt_add_le_sqrt_add_div_sqrt (show (0 : ℝ) < N by positivity)
    (show (0 : ℝ) ≤ H by positivity)
  have hid : ((N : ℝ) + H) / H = (N : ℝ) / H + 1 := by
    have hH' : (H : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hid] at hbound
  linarith

end Sidon

namespace IsSidonSet

theorem card_le_sqrt_add_four_mul_rpow {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ Sidon.interval N) :
    (S.card : ℝ) ≤ Real.sqrt N + 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hNr : (0 : ℝ) < N := by positivity
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let P : ℝ := (N : ℝ) ^ (3 / 4 : ℝ)
  let Q : ℝ := (N : ℝ) ^ (1 / 4 : ℝ)
  let H : ℕ := ⌈P⌉₊
  have hP : 0 < P := Real.rpow_pos_of_pos hNr _
  have hH : 0 < H := Nat.one_le_ceil_iff.mpr hP
  have hHP : P ≤ (H : ℝ) := Nat.le_ceil P
  have hHP' : (H : ℝ) ≤ P + 1 := (Nat.ceil_lt_add_one hP.le).le
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hs₁ : (1 : ℝ) ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN₁
  have hQ₁ : 1 ≤ Q := Real.one_le_rpow hN₁ (by norm_num)
  have hPQ : P / Real.sqrt N = Q := by
    dsimp only [P, Q]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hNr]
    norm_num
  have hNP : (N : ℝ) / P = Q := by
    dsimp only [P, Q]
    calc
      (N : ℝ) / (N : ℝ) ^ (3 / 4 : ℝ) =
          (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) - 3 / 4) := (Real.rpow_sub hNr _ _).symm
      _ = _ := by norm_num
  have hHterm : (H : ℝ) / Real.sqrt N ≤ 2 * Q := by
    have hu := div_le_div_of_nonneg_right hHP' hs.le
    have hone : 1 / Real.sqrt N ≤ 1 := (div_le_one hs).mpr hs₁
    rw [add_div, hPQ] at hu
    linarith
  have hNterm : (N : ℝ) / H ≤ Q := by
    rw [← hNP]
    exact div_le_div_of_nonneg_left hNr.le hP hHP
  have hbound := Sidon.sidon_card_le_window hN hH hS hSN
  change (S.card : ℝ) ≤ Real.sqrt N + 4 * Q
  linarith

end IsSidonSet
