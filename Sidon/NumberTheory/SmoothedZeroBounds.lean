module

public import Sidon.NumberTheory.LowZeroBridge
public import Sidon.NumberTheory.SmoothedExplicitFormula

@[expose] public section

/-! Low and high actual zero estimates for the smoothed explicit formula. -/

noncomputable section

open RiemannGaussian
open scoped BigOperators

namespace Sidon

theorem smoothed_zero_norm_le_occurrences_and_tail (n : ℕ) {T h t : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    ‖∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℂ) *
        spectralSmoothing n h (exponentialZeroAtom (ρ : ℂ)) t‖ ≤
      2 * Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * h ^ (n + 2) *
        (∑ z ∈ zetaZeroOccurrences T,
          Real.exp (-(t + ((n + 2 : ℕ) : ℝ) * h) * (1 - z.1.re))) +
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        ∑' ρ : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
  classical
  let L := t + ((n + 2 : ℕ) : ℝ) * h
  let f : NontrivialZetaZero → ℂ := fun ρ => (analyticZetaZeroMultiplicity ρ : ℂ) *
    spectralSmoothing n h (exponentialZeroAtom (ρ : ℂ)) t
  let lo : NontrivialZetaZero → ℂ := fun ρ => if ‖(ρ : ℂ)‖ < T then f ρ else 0
  let hi : NontrivialZetaZero → ℂ := fun ρ => if T ≤ ‖(ρ : ℂ)‖ then f ρ else 0
  let w : NontrivialZetaZero → ℝ := fun ρ =>
    (analyticZetaZeroMultiplicity ρ : ℝ) * Real.exp (-L * (1 - (ρ : ℂ).re))
  let C := Real.exp L * 2 ^ (n + 2) / T ^ n
  have hL : 0 ≤ L := add_nonneg ht (mul_nonneg (Nat.cast_nonneg _) hh)
  have hlo0 : ∀ ρ, ρ ∉ boundedNontrivialZeros T → lo ρ = 0 := by
    intro ρ hρ
    have hnot : ¬‖(ρ : ℂ)‖ < T := fun h => hρ (mem_boundedNontrivialZeros.mpr h.le)
    simp only [lo, ite_eq_right hnot]
  have hlo : Summable lo := summable_of_ne_finset_zero hlo0
  have hhib : ∀ ρ : NontrivialZetaZero, ‖hi ρ‖ ≤ C *
      ((analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ
    dsimp [hi]
    split_ifs with hρ
    · exact weighted_spectral_atom_norm_le_high (Nat.cast_nonneg _) hT hρ
        (NontrivialZetaZero.zero_lt_re ρ).le (NontrivialZetaZero.re_lt_one ρ).le n hh hL
    · simp only [norm_zero]
      dsimp [C]
      positivity
  have hhiNorm := (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hhib
  have hhi : Summable hi := hhiNorm.of_norm
  have hsplit : (∑' ρ, f ρ) = (∑' ρ, lo ρ) + ∑' ρ, hi ρ := by
    rw [← hlo.tsum_add hhi]
    apply tsum_congr
    intro ρ
    by_cases hρ : ‖(ρ : ℂ)‖ < T
    · simp [lo, hi, hρ, not_le.mpr hρ]
    · simp [lo, hi, hρ, le_of_not_gt hρ]
  have hloPoint : ∀ ρ : NontrivialZetaZero,
      ‖lo ρ‖ ≤ (Real.exp L * h ^ (n + 2)) * w ρ := by
    intro ρ
    dsimp [lo]
    split_ifs
    · dsimp [f]
      rw [norm_mul, Complex.norm_natCast]
      have hb := mul_le_mul_of_nonneg_left
        (spectralSmoothing_exponentialZeroAtom_norm_le (NontrivialZetaZero.coe_ne_zero ρ)
          (NontrivialZetaZero.zero_lt_re ρ).le n hh t)
        (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
      apply hb.trans_eq
      have he : Real.exp ((ρ : ℂ).re * L) = Real.exp L * Real.exp (-L * (1 - (ρ : ℂ).re)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [w]
      change (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.exp ((ρ : ℂ).re * L) * h ^ (n + 2)) = _
      rw [he]
      ring
    · simp only [norm_zero]
      dsimp [w]
      positivity
  have hloBound : ‖∑' ρ, lo ρ‖ ≤
      2 * Real.exp L * h ^ (n + 2) *
        ∑ z ∈ zetaZeroOccurrences T, Real.exp (-L * (1 - z.1.re)) := by
    rw [tsum_eq_sum hlo0]
    calc
      _ ≤ ∑ ρ ∈ boundedNontrivialZeros T, ‖lo ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ boundedNontrivialZeros T, (Real.exp L * h ^ (n + 2)) * w ρ :=
        Finset.sum_le_sum fun ρ _ => hloPoint ρ
      _ = (Real.exp L * h ^ (n + 2)) * ∑ ρ ∈ boundedNontrivialZeros T, w ρ := by
        rw [Finset.mul_sum]
      _ ≤ (Real.exp L * h ^ (n + 2)) *
          (2 * ∑ z ∈ zetaZeroOccurrences T, Real.exp (-L * (1 - z.1.re))) :=
        mul_le_mul_of_nonneg_left
          (sum_boundedNontrivialZeros_le_twice_occurrences T
            (fun z => Real.exp (-L * (1 - z.re))) (fun _ => (Real.exp_pos _).le)
            (fun _ => by simp)) (mul_nonneg (Real.exp_pos _).le (pow_nonneg hh _))
      _ = _ := by ring
  have hhiBound := smoothed_zeta_high_tail_norm_le n hT hh hL
  change ‖∑' ρ, f ρ‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hloBound hhiBound)

end Sidon
