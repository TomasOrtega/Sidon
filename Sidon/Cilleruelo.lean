import Sidon.Analysis.WindowVariance

/-! # Cilleruelo's interval discrepancy estimate -/

noncomputable section

namespace Sidon

def varianceEnvelope (N : ℕ) (S : Finset ℤ) : ℝ :=
  1 + Real.sqrt (sidonDeficit N S) * (N : ℝ) ^ (1 / 8 : ℝ)

theorem sqrt_variance_bound {N H V δ : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hHP : H ≤ N ^ (3 / 4 : ℝ)) (hδ : 0 ≤ δ)
    (hV : V ≤ 2 * H ^ 2 * δ + H ^ 3 / N + 5 * H * Real.sqrt N) :
    Real.sqrt V ≤ 3 * N ^ (5 / 8 : ℝ) * (1 + Real.sqrt δ * N ^ (1 / 8 : ℝ)) := by
  have hpow (a : ℝ) (n : ℕ) : (N ^ a) ^ n = N ^ (a * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have hp2 : (N ^ (3 / 4 : ℝ)) ^ 2 = N ^ (3 / 2 : ℝ) := by
    rw [hpow]
    norm_num
  have hp3 : (N ^ (3 / 4 : ℝ)) ^ 3 / N = N ^ (5 / 4 : ℝ) := by
    rw [hpow]
    calc
      N ^ ((3 / 4 : ℝ) * 3) / N = N ^ (9 / 4 : ℝ) / N ^ (1 : ℝ) := by
        norm_num
      _ = N ^ ((9 / 4 : ℝ) - 1) := (Real.rpow_sub hN _ _).symm
      _ = _ := by norm_num
  have hmul : N ^ (3 / 4 : ℝ) * Real.sqrt N = N ^ (5 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  have hbound : V ≤ 2 * N ^ (3 / 2 : ℝ) * δ + 6 * N ^ (5 / 4 : ℝ) := by
    calc
      V ≤ 2 * H ^ 2 * δ + H ^ 3 / N + 5 * H * Real.sqrt N := hV
      _ ≤ 2 * (N ^ (3 / 4 : ℝ)) ^ 2 * δ +
          (N ^ (3 / 4 : ℝ)) ^ 3 / N + 5 * N ^ (3 / 4 : ℝ) * Real.sqrt N := by
        gcongr
      _ = _ := by rw [hp2, hp3, mul_assoc 5, hmul]; ring
  let a : ℝ := Real.sqrt δ * N ^ (1 / 8 : ℝ)
  have ha : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = δ * N ^ (1 / 4 : ℝ) := by
    dsimp only [a]
    rw [mul_pow, Real.sq_sqrt hδ, hpow]
    norm_num
  have hsplit : N ^ (3 / 2 : ℝ) = N ^ (5 / 4 : ℝ) * N ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN]
    norm_num
  have hpoly : 6 + 2 * a ^ 2 ≤ 9 * (1 + a) ^ 2 := by nlinarith
  have hpoly' := mul_le_mul_of_nonneg_left hpoly
    (Real.rpow_nonneg hN.le (5 / 4 : ℝ))
  have hbound' : V ≤ 9 * N ^ (5 / 4 : ℝ) * (1 + a) ^ 2 := by
    rw [ha2] at hpoly'
    rw [hsplit] at hbound
    nlinarith
  have hsq : (3 * N ^ (5 / 8 : ℝ) * (1 + a)) ^ 2 =
      9 * N ^ (5 / 4 : ℝ) * (1 + a) ^ 2 := by
    rw [mul_pow, mul_pow, hpow]
    norm_num
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [hsq]
  exact hbound'

theorem optimized_windowVariance_sqrt_le {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    Real.sqrt (windowVariance N ⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ S) ≤
      3 * (N : ℝ) ^ (5 / 8 : ℝ) * varianceEnvelope N S := by
  have hw := floor_rpow_window_spec hN (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1)
  exact sqrt_variance_bound (by positivity) (by positivity) hw.2.2.2
    (deficit_nonneg N S) (sidon_windowVariance_le hN hw.1 hS hSN)

theorem optimized_windowVariance_sqrt_div_le {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    Real.sqrt (windowVariance N ⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ S) /
      (⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ) ≤
      6 * (N : ℝ) ^ (-(1 / 8 : ℝ)) * varianceEnvelope N S := by
  have hw := floor_rpow_window_spec hN (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hNr : (0 : ℝ) < N := by positivity
  have hpow : 0 < (N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hfirst := optimized_windowVariance_sqrt_le hN hS hSN
  have hH : (0 : ℝ) < (⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hw.1
  have hquot : (N : ℝ) ^ (5 / 8 : ℝ) / (N : ℝ) ^ (3 / 4 : ℝ) =
      (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [← Real.rpow_sub hNr]
    norm_num
  calc
    _ ≤ (3 * (N : ℝ) ^ (5 / 8 : ℝ) * varianceEnvelope N S) /
        (⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ) :=
      div_le_div_of_nonneg_right hfirst hH.le
    _ ≤ (3 * (N : ℝ) ^ (5 / 8 : ℝ) * varianceEnvelope N S) /
        ((N : ℝ) ^ (3 / 4 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by unfold varianceEnvelope; positivity)
        (by positivity) hw.2.2.1
    _ = 6 * ((N : ℝ) ^ (5 / 8 : ℝ) / (N : ℝ) ^ (3 / 4 : ℝ)) *
        varianceEnvelope N S := by ring
    _ = _ := by rw [hquot]

theorem card_Icc_add_length (a : ℤ) (L : ℕ) :
    (Finset.Icc (a + 1) (a + L)).card = L := by
  rw [Int.card_Icc]
  omega

theorem expanded_window_mean_le {N H L m : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hm : 0 ≤ m) :
    (L + H) * m / (N + H) - L * m / N ≤ H * m / N := by
  have hdiv : (L + H) * m / (N + H) ≤ (L + H) * m / N :=
    div_le_div_of_nonneg_left (by positivity) hN (by linarith)
  have hid : (L + H) * m / N = L * m / N + H * m / N := by ring
  linarith

theorem contracted_window_mean_le {N H L m : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hLN : L ≤ N) (hm : 0 ≤ m) :
    L * m / N - (L - H) * m / (N + H) ≤ 2 * H * m / N := by
  have hT : 0 < N + H := by positivity
  have hnum : N + L ≤ 2 * (N + H) := by linarith
  calc
    L * m / N - (L - H) * m / (N + H) =
        H * m * (N + L) / (N * (N + H)) := by field_simp; ring
    _ ≤ H * m * (2 * (N + H)) / (N * (N + H)) := by gcongr
    _ = _ := by field_simp; ring

theorem interval_discrepancy_le_window {N H L : ℕ} (hN : 0 < N) (hH : 0 < H)
    (S : Finset ℤ) (a : ℤ) (ha : 0 ≤ a) (haL : a + L ≤ N) :
    |((S ∩ Finset.Icc (a + 1) (a + L)).card : ℝ) - (L : ℝ) * S.card / N| ≤
      2 * (H : ℝ) * S.card / N +
        (Real.sqrt L + Real.sqrt H) * Real.sqrt (windowVariance N H S) / H := by
  classical
  let I := Finset.Icc (a + 1) (a + L)
  let U := Finset.Icc (a + 1) (a + (L + H : ℕ))
  let m : ℝ := S.card
  let k : ℝ := (S ∩ I).card
  let T : ℝ := (N + H : ℕ)
  let v : ℝ := (H : ℝ) * m / T
  let V : ℝ := windowVariance N H S
  have hNr : (0 : ℝ) < N := by positivity
  have hHr : (0 : ℝ) < H := by positivity
  have hTr : 0 < T := by dsimp only [T]; positivity
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hLN : L ≤ N := by omega
  have hT : T = (N : ℝ) + H := by simp only [T, Nat.cast_add]
  have hfilter : (S.filter fun s => s ∈ I) = S ∩ I := by ext x; simp
  have hU : U ⊆ interval (N + H) := by
    intro t ht
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_Icc.mp ht
    exact mem_interval.mpr ⟨by omega, by omega⟩
  have hUcard : (U.card : ℝ) = (L : ℝ) + H := by
    have hh : U.card = L + H := card_Icc_add_length a (L + H)
    exact_mod_cast hh
  have hcountU : (H : ℝ) * k ≤ ∑ t ∈ U, windowCount H S t := by
    have hh := sum_windowCount_ge_card H S U (fun s => s ∈ I) (by
      intro s hs hsI u hu
      have hs' := Finset.mem_Icc.mp hsI
      have hu' := Finset.mem_range.mp hu
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simpa only [hfilter] using hh
  have hcsU : |∑ t ∈ U, (windowCount H S t - v)| ≤
      Real.sqrt U.card * Real.sqrt V := abs_sum_windowCount_sub_le S U hU
  have hsumU : (∑ t ∈ U, windowCount H S t) =
      (U.card : ℝ) * v + ∑ t ∈ U, (windowCount H S t - v) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hupperK : k ≤ ((L : ℝ) + H) * m / T +
      Real.sqrt U.card * Real.sqrt V / H := by
    apply (mul_le_mul_left hHr).mp
    have he : (U.card : ℝ) * v = (H : ℝ) * (((L : ℝ) + H) * m / T) := by
      rw [hUcard]
      dsimp only [v]
      ring
    calc
      (H : ℝ) * k ≤ (U.card : ℝ) * v + Real.sqrt U.card * Real.sqrt V := by
        linarith [le_abs_self (∑ t ∈ U, (windowCount H S t - v))]
      _ = (H : ℝ) * (((L : ℝ) + H) * m / T +
          Real.sqrt U.card * Real.sqrt V / H) := by
        rw [he]
        field_simp
        ring
  have hrootU : Real.sqrt U.card ≤ Real.sqrt L + Real.sqrt H := by
    rw [hUcard]
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [add_sq, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (L : ℝ)) (Real.sqrt_nonneg (H : ℝ))]
  have hupper : k - (L : ℝ) * m / N ≤ (H : ℝ) * m / N +
      (Real.sqrt L + Real.sqrt H) * Real.sqrt V / H := by
    have hmean := expanded_window_mean_le hNr hHr.le (Nat.cast_nonneg L) hm
    rw [← hT] at hmean
    have hroot : Real.sqrt U.card * Real.sqrt V / H ≤
        (Real.sqrt L + Real.sqrt H) * Real.sqrt V / H := by gcongr
    linarith
  have hterm : 0 ≤ (Real.sqrt L + Real.sqrt H) * Real.sqrt V / (H : ℝ) := by positivity
  have hbias : 0 ≤ (H : ℝ) * m / N := by positivity
  change |k - (L : ℝ) * m / N| ≤ 2 * (H : ℝ) * m / N +
    (Real.sqrt L + Real.sqrt H) * Real.sqrt V / H
  apply abs_le.mpr
  constructor
  · suffices (L : ℝ) * m / N - k ≤ 2 * (H : ℝ) * m / N +
        (Real.sqrt L + Real.sqrt H) * Real.sqrt V / H by linarith
    by_cases hLH : H ≤ L
    · let W := Finset.Icc (a + (H : ℤ) + 1) (a + L)
      have hW : W ⊆ interval (N + H) := by
        intro t ht
        obtain ⟨ht₁, ht₂⟩ := Finset.mem_Icc.mp ht
        exact mem_interval.mpr ⟨by omega, by omega⟩
      have hWcard : (W.card : ℝ) = (L : ℝ) - H := by
        have hw : (W.card : ℤ) = (L : ℤ) - H := by
          dsimp only [W]
          rw [Int.card_Icc_of_le (a + (H : ℤ) + 1) (a + L) (by omega)]
          omega
        exact_mod_cast hw
      have hcountW : (∑ t ∈ W, windowCount H S t) ≤ (H : ℝ) * k := by
        have hh := sum_windowCount_le_card H S W (fun s => s ∈ I) (by
          intro s hs u hu hmem
          have hs' := Finset.mem_Icc.mp hmem
          have hu' := Finset.mem_range.mp hu
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        simpa only [hfilter] using hh
      have hcsW : |∑ t ∈ W, (windowCount H S t - v)| ≤
          Real.sqrt W.card * Real.sqrt V := abs_sum_windowCount_sub_le S W hW
      have hsumW : (∑ t ∈ W, windowCount H S t) =
          (W.card : ℝ) * v + ∑ t ∈ W, (windowCount H S t - v) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
      have hlowerK : ((L : ℝ) - H) * m / T - Real.sqrt W.card * Real.sqrt V / H ≤ k := by
        apply (mul_le_mul_left hHr).mp
        have he : (W.card : ℝ) * v = (H : ℝ) * (((L : ℝ) - H) * m / T) := by
          rw [hWcard]
          dsimp only [v]
          ring
        have hcount' : (W.card : ℝ) * v - Real.sqrt W.card * Real.sqrt V ≤ (H : ℝ) * k := by
          linarith [neg_le_abs (∑ t ∈ W, (windowCount H S t - v))]
        calc
          (H : ℝ) * (((L : ℝ) - H) * m / T - Real.sqrt W.card * Real.sqrt V / H) =
              (W.card : ℝ) * v - Real.sqrt W.card * Real.sqrt V := by
            rw [he]
            field_simp
            ring
          _ ≤ _ := hcount'
      have hmean := contracted_window_mean_le hNr hHr.le
        (show (L : ℝ) ≤ N by exact_mod_cast hLN) hm
      rw [← hT] at hmean
      have hrootW : Real.sqrt W.card ≤ Real.sqrt L + Real.sqrt H := by
        have hh : (W.card : ℝ) ≤ L := by
          rw [hWcard]
          linarith [Nat.cast_nonneg (α := ℝ) H]
        have := Real.sqrt_le_sqrt hh
        linarith [Real.sqrt_nonneg (H : ℝ)]
      have hroot : Real.sqrt W.card * Real.sqrt V / H ≤
          (Real.sqrt L + Real.sqrt H) * Real.sqrt V / H := by gcongr
      linarith
    · have hL : (L : ℝ) ≤ H := by exact_mod_cast (le_of_lt (lt_of_not_ge hLH))
      have hsmall : (L : ℝ) * m / N ≤ (H : ℝ) * m / N := by gcongr
      ring_nf at hsmall hbias hterm ⊢
      linarith
  · ring_nf at hupper hbias ⊢
    linarith

theorem three_quarter_window_bias_le {N H : ℝ} (hN : 0 < N)
    (hHP : H ≤ N ^ (3 / 4 : ℝ)) {m : ℝ} (hm₀ : 0 ≤ m)
    (hm : m ≤ 5 * Real.sqrt N) : H * m / N ≤ 5 * N ^ (1 / 4 : ℝ) := by
  have heq : N ^ (3 / 4 : ℝ) * Real.sqrt N / N = N ^ (1 / 4 : ℝ) := by
    calc
      N ^ (3 / 4 : ℝ) * Real.sqrt N / N =
          N ^ ((3 / 4 : ℝ) + 1 / 2) / N ^ (1 : ℝ) := by
        rw [Real.rpow_add hN, ← Real.sqrt_eq_rpow, Real.rpow_one]
      _ = N ^ (((3 / 4 : ℝ) + 1 / 2) - 1) := (Real.rpow_sub hN _ _).symm
      _ = _ := by norm_num
  calc
    H * m / N ≤ N ^ (3 / 4 : ℝ) * (5 * Real.sqrt N) / N := by gcongr
    _ = 5 * (N ^ (3 / 4 : ℝ) * Real.sqrt N / N) := by ring
    _ = _ := by rw [heq]

theorem cilleruelo_interval_estimate {N L : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (a : ℤ)
    (ha : 0 ≤ a) (haL : a + L ≤ N) :
    |((S ∩ Finset.Icc (a + 1) (a + L)).card : ℝ) - (L : ℝ) * S.card / N| ≤
      16 * ((N : ℝ) ^ (1 / 4 : ℝ) + Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ))) *
        varianceEnvelope N S := by
  let H := ⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊
  let B : ℝ := (N : ℝ) ^ (1 / 4 : ℝ) + Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ))
  let R : ℝ := varianceEnvelope N S
  have hw := floor_rpow_window_spec hN (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hH : 0 < H := hw.1
  have hNr : (0 : ℝ) < N := by positivity
  have hHr : (0 : ℝ) < H := by positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hR : 1 ≤ R := by
    dsimp only [R, varianceEnvelope]
    exact le_add_of_nonneg_right (by positivity)
  have hR₀ : 0 ≤ R := by linarith
  have hbase := interval_discrepancy_le_window hN hH S a ha haL
  have hbias := three_quarter_window_bias_le hNr hw.2.2.2
    (show (0 : ℝ) ≤ S.card by positivity) (hS.card_le_five_mul_sqrt hSN)
  have hvariance := optimized_windowVariance_sqrt_div_le hN hS hSN
  have hsqrt : Real.sqrt (H : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) := by
    calc
      Real.sqrt (H : ℝ) ≤ Real.sqrt ((N : ℝ) ^ (3 / 4 : ℝ)) :=
        Real.sqrt_le_sqrt hw.2.2.2
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNr.le]
        norm_num
  have hpower : (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ)) =
      (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hterm : (Real.sqrt L + Real.sqrt H) * Real.sqrt (windowVariance N H S) / H ≤
      6 * B * R := by
    calc
      (Real.sqrt L + Real.sqrt H) * Real.sqrt (windowVariance N H S) / H =
          (Real.sqrt L + Real.sqrt H) * (Real.sqrt (windowVariance N H S) / H) := by ring
      _ ≤ (Real.sqrt L + (N : ℝ) ^ (3 / 8 : ℝ)) *
          (6 * (N : ℝ) ^ (-(1 / 8 : ℝ)) * R) := by gcongr
      _ = 6 * (Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ)) +
          (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ))) * R := by ring
      _ = 6 * B * R := by rw [hpower]; dsimp only [B]; ring
  have hBR : (N : ℝ) ^ (1 / 4 : ℝ) ≤ B * R := by
    calc
      (N : ℝ) ^ (1 / 4 : ℝ) ≤ B := by
        dsimp only [B]
        exact le_add_of_nonneg_right (by positivity)
      _ ≤ B * R := le_mul_of_one_le_right hB hR
  change |((S ∩ Finset.Icc (a + 1) (a + L)).card : ℝ) - (L : ℝ) * S.card / N| ≤
    16 * B * R
  ring_nf at hbase hbias hterm hBR ⊢
  linarith only [hbase, hbias, hterm, hBR]

theorem cilleruelo_short_interval {N L : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (a : ℤ)
    (ha : 0 ≤ a) (haL : a + L ≤ N) (hL : (L : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ)) :
    ((S ∩ Finset.Icc (a + 1) (a + L)).card : ℝ) ≤
      37 * ((N : ℝ) ^ (1 / 4 : ℝ) +
        Real.sqrt |1 - (S.card : ℝ) / Real.sqrt N| * (N : ℝ) ^ (3 / 8 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by positivity
  have hdis := cilleruelo_interval_estimate hN hS hSN a ha haL
  have hmain := three_quarter_window_bias_le hNr hL
    (show (0 : ℝ) ≤ S.card by positivity) (hS.card_le_five_mul_sqrt hSN)
  have hroot : Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ)) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ)) ≤
          Real.sqrt ((N : ℝ) ^ (3 / 4 : ℝ)) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by gcongr
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNr.le, ← Real.rpow_add hNr]
        norm_num
  have hδ : sidonDeficit N S ≤ |1 - (S.card : ℝ) / Real.sqrt N| := by
    exact max_le (abs_nonneg _) (le_abs_self _)
  have hδsqrt := Real.sqrt_le_sqrt hδ
  have hR₀ : 0 ≤ varianceEnvelope N S := by unfold varianceEnvelope; positivity
  have hfactor : ((N : ℝ) ^ (1 / 4 : ℝ) + Real.sqrt L * (N : ℝ) ^ (-(1 / 8 : ℝ))) *
      varianceEnvelope N S ≤ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * varianceEnvelope N S := by
    exact mul_le_mul_of_nonneg_right (by linarith) hR₀
  have hp : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) =
      (N : ℝ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hscaled : (N : ℝ) ^ (1 / 4 : ℝ) * varianceEnvelope N S ≤
      (N : ℝ) ^ (1 / 4 : ℝ) +
        Real.sqrt |1 - (S.card : ℝ) / Real.sqrt N| * (N : ℝ) ^ (3 / 8 : ℝ) := by
    unfold varianceEnvelope
    calc
      (N : ℝ) ^ (1 / 4 : ℝ) *
          (1 + Real.sqrt (sidonDeficit N S) * (N : ℝ) ^ (1 / 8 : ℝ)) =
          (N : ℝ) ^ (1 / 4 : ℝ) +
            Real.sqrt (sidonDeficit N S) * (N : ℝ) ^ (3 / 8 : ℝ) := by
        calc
          _ = (N : ℝ) ^ (1 / 4 : ℝ) + Real.sqrt (sidonDeficit N S) *
              ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ)) := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by gcongr
  have hnonneg : 0 ≤ Real.sqrt |1 - (S.card : ℝ) / Real.sqrt N| *
      (N : ℝ) ^ (3 / 8 : ℝ) := by positivity
  have hupper := le_abs_self (((S ∩ Finset.Icc (a + 1) (a + L)).card : ℝ) -
    (L : ℝ) * S.card / N)
  ring_nf at hdis hmain hfactor hscaled hnonneg hupper ⊢
  linarith only [hdis, hmain, hfactor, hscaled, hnonneg, hupper]

end Sidon
