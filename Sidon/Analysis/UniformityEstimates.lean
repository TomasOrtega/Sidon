import Sidon.Analysis.PowerWindow
import Mathlib.Tactic

/-! # Arithmetic estimates for the Fourier-uniformity argument -/

namespace Sidon

theorem normalized_square_deviation_le {N m : ℝ} (hN : 0 < N) (hm₀ : 0 ≤ m)
    (hm : m ≤ 5 * Real.sqrt N) :
    |m ^ 2 / N - 1| ≤ 6 * |m / Real.sqrt N - 1| := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hq₀ : 0 ≤ m / Real.sqrt N := div_nonneg hm₀ hs.le
  have hq₅ : m / Real.sqrt N ≤ 5 := (div_le_iff₀ hs).mpr hm
  have hdiv : m ^ 2 / N = (m / Real.sqrt N) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hN.le]
  have heq : m ^ 2 / N - 1 = (m / Real.sqrt N - 1) * (m / Real.sqrt N + 1) := by
    rw [hdiv]
    ring
  rw [heq, abs_mul, abs_of_nonneg (by linarith : 0 ≤ m / Real.sqrt N + 1)]
  nlinarith [abs_nonneg (m / Real.sqrt N - 1)]

/-- The four correlation errors cancel their common main term. -/
theorem fourier_error_master_le {N H m E₁₁ E₂₂ E₁₂ E₂₁ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hHN : H ≤ N) (hm₀ : 0 ≤ m)
    (hm : m ≤ 5 * Real.sqrt N)
    (h₁₁ : E₁₁ ≤ 2 * |m ^ 2 / N - 1| + m ^ 2 * H / N ^ 2 + 2 * m / H)
    (h₂₂ : E₂₂ ≤ m ^ 2 * H / N ^ 2)
    (h₁₂ : E₁₂ ≤ 5 * m * Real.sqrt H / N)
    (h₂₁ : E₂₁ ≤ 5 * m * Real.sqrt H / N) :
    (N + H) * (E₁₁ + E₂₂ + E₁₂ + E₂₁) ≤
      24 * N * |m / Real.sqrt N - 1| + 20 * N * Real.sqrt N / H +
        200 * Real.sqrt N * Real.sqrt H := by
  have hsN := Real.sqrt_nonneg N
  have hsH := Real.sqrt_nonneg H
  have hsqN := Real.sq_sqrt hN.le
  have hsqH := Real.sq_sqrt hH.le
  have hdev := normalized_square_deviation_le hN hm₀ hm
  have hmSq : m ^ 2 ≤ 25 * N := by nlinarith
  have hterm : m ^ 2 * H / N ^ 2 ≤ 25 * H / N := by
    apply (div_le_div_iff (sq_pos_of_pos hN) hN).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmSq (mul_nonneg hH.le hN.le)]
  have htermH : 2 * m / H ≤ 10 * Real.sqrt N / H := by
    exact div_le_div_of_nonneg_right (by linarith) hH.le
  have htermMixed : 5 * m * Real.sqrt H / N ≤
      25 * Real.sqrt N * Real.sqrt H / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    nlinarith [mul_le_mul_of_nonneg_right hm hsH]
  have hsum : E₁₁ + E₂₂ + E₁₂ + E₂₁ ≤
      12 * |m / Real.sqrt N - 1| + 50 * H / N + 10 * Real.sqrt N / H +
        50 * Real.sqrt N * Real.sqrt H / N := by
    ring_nf at h₁₁ h₂₂ h₁₂ h₂₁ hdev hterm htermH htermMixed ⊢
    linarith only [h₁₁, h₂₂, h₁₂, h₂₁, hdev, hterm, htermH, htermMixed]
  have hsum₀ : 0 ≤ 12 * |m / Real.sqrt N - 1| + 50 * H / N +
      10 * Real.sqrt N / H + 50 * Real.sqrt N * Real.sqrt H / N := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ N + H)
  have hscaled' := mul_le_mul_of_nonneg_right (by linarith : N + H ≤ 2 * N) hsum₀
  have hroot : H ≤ Real.sqrt N * Real.sqrt H := by
    have := Real.sqrt_le_sqrt hHN
    nlinarith [mul_le_mul_of_nonneg_right this hsH]
  have hidentity : 2 * N * (12 * |m / Real.sqrt N - 1| + 50 * H / N +
      10 * Real.sqrt N / H + 50 * Real.sqrt N * Real.sqrt H / N) =
      24 * N * |m / Real.sqrt N - 1| + 100 * H +
        20 * N * Real.sqrt N / H + 100 * Real.sqrt N * Real.sqrt H := by
    field_simp [ne_of_gt hN, ne_of_gt hH]
    ring
  rw [hidentity] at hscaled'
  linarith

/-- The window upper bound controls the square-root boundary error. -/
theorem sqrt_window_error_le {N H : ℝ} (hN : 0 < N)
    (hH : H ≤ N ^ (2 / 3 : ℝ)) :
    Real.sqrt N * Real.sqrt H ≤ N ^ (5 / 6 : ℝ) := by
  calc
    Real.sqrt N * Real.sqrt H ≤ Real.sqrt N * Real.sqrt (N ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) (Real.sqrt_nonneg N)
    _ = N ^ (5 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le,
        ← Real.rpow_add hN]
      norm_num

/-- The window lower bound controls the diagonal error. -/
theorem diagonal_window_error_le {N H : ℝ} (hN : 0 < N)
    (hH : N ^ (2 / 3 : ℝ) / 2 ≤ H) :
    N * Real.sqrt N / H ≤ 2 * N ^ (5 / 6 : ℝ) := by
  have hp : 0 < N ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hN _
  have heq : N * Real.sqrt N / N ^ (2 / 3 : ℝ) = N ^ (5 / 6 : ℝ) := by
    calc
      N * Real.sqrt N / N ^ (2 / 3 : ℝ) =
          N ^ ((1 : ℝ) + 1 / 2) / N ^ (2 / 3 : ℝ) := by
        rw [Real.rpow_add hN, Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ = N ^ ((1 : ℝ) + 1 / 2 - 2 / 3) := (Real.rpow_sub hN _ _).symm
      _ = N ^ (5 / 6 : ℝ) := by norm_num
  calc
    N * Real.sqrt N / H ≤ N * Real.sqrt N / (N ^ (2 / 3 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hN.le (Real.sqrt_nonneg N))
        (by positivity) hH
    _ = 2 * (N * Real.sqrt N / N ^ (2 / 3 : ℝ)) := by field_simp; ring
    _ = 2 * N ^ (5 / 6 : ℝ) := by rw [heq]

/-- Optimizing the integer window preserves the stated absolute constant. -/
theorem optimized_fourier_error_le {N : ℕ} (hN : 0 < N) {δ x : ℝ} (hδ : 0 ≤ δ)
    (hwindow : ∀ H : ℕ, 0 < H → H ≤ N →
      x ^ 2 ≤ 24 * N * δ + 20 * N * Real.sqrt N / H +
        200 * Real.sqrt N * Real.sqrt H) :
    x ^ 2 ≤ 240 * N * (δ + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let H := ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊
  have hs := floor_rpow_window_spec hN (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hH : 0 < H := hs.1
  have hHN : H ≤ N := hs.2.1
  have hdiag := diagonal_window_error_le hNr hs.2.2.1
  have hroot := sqrt_window_error_le hNr hs.2.2.2
  have hbound := hwindow H hH hHN
  have hpower : (N : ℝ) ^ (5 / 6 : ℝ) = (N : ℝ) * (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
    calc
      (N : ℝ) ^ (5 / 6 : ℝ) = (N : ℝ) ^ ((1 : ℝ) + -(1 / 6 : ℝ)) := by norm_num
      _ = (N : ℝ) * (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
        rw [Real.rpow_add hNr, Real.rpow_one]
  change (N : ℝ) * Real.sqrt N / H ≤ 2 * (N : ℝ) ^ (5 / 6 : ℝ) at hdiag
  change Real.sqrt N * Real.sqrt H ≤ (N : ℝ) ^ (5 / 6 : ℝ) at hroot
  rw [hpower] at hdiag hroot
  ring_nf at hbound hdiag hroot ⊢
  nlinarith [mul_nonneg hNr.le hδ]

/-- Passing from the optimized squared estimate to the paper's square-root bound. -/
theorem fourier_uniformity_of_window_estimates {N : ℕ} (hN : 0 < N)
    {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (hwindow : ∀ H : ℕ, 0 < H → H ≤ N →
      x ^ 2 ≤ 24 * N * δ + 20 * N * Real.sqrt N / H +
        200 * Real.sqrt N * Real.sqrt H) :
    x ≤ 16 * Real.sqrt N * Real.sqrt (δ + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hE : 0 ≤ δ + (N : ℝ) ^ (-(1 / 6 : ℝ)) :=
    add_nonneg hδ (Real.rpow_nonneg hNr _)
  have hbound := optimized_fourier_error_le hN hδ hwindow
  have hsq : (16 * Real.sqrt N * Real.sqrt (δ + (N : ℝ) ^ (-(1 / 6 : ℝ)))) ^ 2 =
      256 * N * (δ + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hNr, Real.sq_sqrt hE]
    norm_num
  have htarget : 0 ≤ 16 * Real.sqrt N * Real.sqrt (δ + (N : ℝ) ^ (-(1 / 6 : ℝ))) :=
    by positivity
  have hle : x ^ 2 ≤
      (16 * Real.sqrt N * Real.sqrt (δ + (N : ℝ) ^ (-(1 / 6 : ℝ)))) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg hNr hE]
  simpa only [abs_of_nonneg hx, abs_of_nonneg htarget] using sq_le_sq.mp hle

end Sidon
