/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.FiniteShiftCorrelation
import Sidon.NumberTheory.RiemannGaussian.FiniteVanDerCorput

namespace RiemannGaussian.FiniteVanDerCorputPhase
noncomputable section
open Complex RiemannGaussian.FiniteShiftCorrelation
open scoped Classical

def windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico a (a + N) then b n else 0

theorem windowed_on (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {n : ℤ}
    (hn : n ∈ Finset.Ico a (a + N)) : windowed a N b n = b n := by
  simp only [windowed, ite_eq_left hn]

theorem windowed_outside (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    ∀ n ∉ Finset.Ico a (a + N), windowed a N b n = 0 := by
  intro n hn
  simp only [windowed, ite_eq_right hn]

theorem sum_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), windowed a N b n) =
      ∑ n ∈ Finset.Ico a (a + N), b n :=
  Finset.sum_congr rfl (fun _ hn ↦ windowed_on a N b hn)

theorem energy_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), ‖windowed a N b n‖ ^ 2) =
      ∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2 :=
  Finset.sum_congr rfl (fun _ hn ↦ by rw [windowed_on a N b hn])

theorem correlation_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {h : ℤ} (hh : 0 ≤ h) :
    correlation (windowed a N b) h =
      ∑ n ∈ Finset.Ico a (a + N - h), b (n + h) * starRingEnd ℂ (b n) := by
  calc
    _ = ∑ n ∈ Finset.Ico a (a + N - h),
        windowed a N b (n + h) * starRingEnd ℂ (windowed a N b n) := by
      apply tsum_eq_sum
      intro n hn
      by_cases hb : n ∈ Finset.Ico a (a + N)
      · have hs : n + h ∉ Finset.Ico a (a + N) := by
          simp only [Finset.mem_Ico] at hb hn ⊢
          omega
        simp only [windowed, ite_eq_right hs, zero_mul]
      · simp only [windowed, ite_eq_right hb, map_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hb : n ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      have hs : n + h ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      rw [windowed_on a N b hb, windowed_on a N b hs]

theorem absolute_window_bound (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), b n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            b (n + ((h : ℤ) + 1)) * starRingEnd ℂ (b n)‖) := by
  have h := FiniteVanDerCorput.absolute_bound hH (windowed_outside a N b)
  rw [sum_windowed, energy_windowed] at h
  have hc (k : ℕ) := correlation_windowed a N b (h := (k : ℤ) + 1) (by omega)
  simpa only [hc] using h

def phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) : ℂ :=
  w n * Complex.exp ((φ n : ℂ) * Complex.I)

theorem norm_phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) :
    ‖phaseTerm w φ n‖ = ‖w n‖ := by
  rw [phaseTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem phaseTerm_pair (w : ℤ → ℂ) (φ : ℤ → ℝ) (n h : ℤ) :
    phaseTerm w φ (n + h) * starRingEnd ℂ (phaseTerm w φ n) =
      (w (n + h) * starRingEnd ℂ (w n)) *
        Complex.exp (((φ (n + h) - φ n : ℝ) : ℂ) * Complex.I) := by
  simp only [phaseTerm, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem absolute_phase_bound (a : ℤ) (N : ℕ) (w : ℤ → ℂ) (φ : ℤ → ℝ)
    {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), phaseTerm w φ n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖w n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            (w (n + ((h : ℤ) + 1)) * starRingEnd ℂ (w n)) *
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  simpa only [norm_phaseTerm, phaseTerm_pair] using
    absolute_window_bound a N (phaseTerm w φ) hH

theorem unit_phase_bound (a : ℤ) (N : ℕ) (φ : ℤ → ℝ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N),
      Complex.exp ((φ n : ℂ) * Complex.I)‖ ^ 2 ≤
        ((N : ℝ) + H - 1) * ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
            ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  have hc : (Finset.Ico a (a + N)).card = N := by
    rw [Int.card_Ico]
    simp
  simpa only [phaseTerm, map_one, one_mul, norm_one, one_pow,
    Finset.sum_const, hc, nsmul_eq_mul, mul_one] using
      absolute_phase_bound a N (fun _ ↦ 1) φ hH

end
end RiemannGaussian.FiniteVanDerCorputPhase
