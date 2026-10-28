module

public import Sidon.NumberTheory.SpectralKernelBounds

@[expose] public section

/-! High-zero tails controlled by a summable reciprocal-square mass. -/

noncomputable section

namespace Sidon

theorem weighted_spectral_atom_norm_le_high {z : ℂ} {m T h t : ℝ}
    (hm : 0 ≤ m) (hT : 0 < T) (hzT : T ≤ ‖z‖)
    (hβ : 0 ≤ z.re) (hβ1 : z.re ≤ 1) (n : ℕ) (hh : 0 ≤ h)
    (hwindow : 0 ≤ t + ((n + 2 : ℕ) : ℝ) * h) :
    ‖(m : ℂ) * spectralSmoothing n h (exponentialZeroAtom z) t‖ ≤
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        (m / ‖z‖ ^ 2) := by
  have hzpos : 0 < ‖z‖ := hT.trans_le hzT
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
  have he : Real.exp (z.re * (t + ((n + 2 : ℕ) : ℝ) * h)) ≤
      Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) := by
    apply Real.exp_le_exp.mpr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ1 hwindow
  calc
    _ ≤ m * (Real.exp (z.re * (t + ((n + 2 : ℕ) : ℝ) * h)) *
        2 ^ (n + 2) / ‖z‖ ^ (n + 2)) :=
      mul_le_mul_of_nonneg_left
        (spectralSmoothing_exponentialZeroAtom_norm_le_high hz hβ n hh t) hm
    _ ≤ m * (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) *
        2 ^ (n + 2) / ‖z‖ ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity)) hm
    _ = (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) *
        (m / ‖z‖ ^ 2)) / ‖z‖ ^ n := by rw [pow_add]; ring
    _ ≤ (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) *
        (m / ‖z‖ ^ 2)) / T ^ n :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hT n)
        (pow_le_pow_left₀ hT.le hzT n)
    _ = _ := by ring

theorem norm_spectral_tail_le_square_mass {ι : Type*} (z : ι → ℂ) (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hβ : ∀ i, 0 ≤ (z i).re) (hβ1 : ∀ i, (z i).re ≤ 1)
    (hmass : Summable (fun i => m i / ‖z i‖ ^ 2)) (n : ℕ) {T h t : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (hwindow : 0 ≤ t + ((n + 2 : ℕ) : ℝ) * h) :
    ‖∑' i, if T ≤ ‖z i‖ then
        (m i : ℂ) * spectralSmoothing n h (exponentialZeroAtom (z i)) t else 0‖ ≤
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        ∑' i, m i / ‖z i‖ ^ 2 := by
  let C := Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n
  let f : ι → ℂ := fun i => if T ≤ ‖z i‖ then
    (m i : ℂ) * spectralSmoothing n h (exponentialZeroAtom (z i)) t else 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ i, ‖f i‖ ≤ C * (m i / ‖z i‖ ^ 2) := by
    intro i
    dsimp [f]
    split_ifs with hi
    · exact weighted_spectral_atom_norm_le_high (hm i) hT hi (hβ i) (hβ1 i) n hh hwindow
    · simp only [norm_zero]
      exact mul_nonneg hC (div_nonneg (hm i) (sq_nonneg _))
  have hsum := (hmass.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' i, C * (m i / ‖z i‖ ^ 2) := hsum.tsum_le_tsum hb (hmass.mul_left C)
    _ = _ := tsum_mul_left

end Sidon
