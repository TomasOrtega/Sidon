import Sidon.NumberTheory.SmoothedZeroBounds
import Sidon.NumberTheory.SmoothedPrimeDetection

/-! The exact arithmetic lower estimate furnished by the smoothed explicit formula. -/

noncomputable section

open RiemannGaussian
open scoped BigOperators

namespace Sidon

theorem smoothed_detector_lower_estimate (n : ℕ) {T h t : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    Real.exp t * (Real.exp h - 1) ^ (n + 2) ≤
      (fwdDiff h)^[n + 2] (smoothedMangoldt n) t +
      2 * Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * h ^ (n + 2) *
        (∑ z ∈ zetaZeroOccurrences T,
          Real.exp (-(t + ((n + 2 : ℕ) : ℝ) * h) * (1 - z.1.re))) +
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        (∑' ρ : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) +
      (Real.pi ^ 2 / 6) * h ^ n := by
  let Z : ℂ := ∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℂ) *
    spectralSmoothing n h (exponentialZeroAtom (ρ : ℂ)) t
  let V := spectralSmoothing n h RosserSchoenfeldTrivialPrimitive.value t
  have hsum : Z = ∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℂ) *
      (Complex.exp ((ρ : ℂ) * t) *
        ((Complex.exp ((ρ : ℂ) * h) - 1) / (ρ : ℂ)) ^ (n + 2)) := by
    apply tsum_congr
    intro ρ
    rw [spectralSmoothing_exponentialZeroAtom (NontrivialZetaZero.coe_ne_zero ρ)]
  have hmain : Complex.exp (t : ℂ) * (Complex.exp (h : ℂ) - 1) ^ (n + 2) =
      ((Real.exp t * (Real.exp h - 1) ^ (n + 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  have he := smoothed_explicit_formula n hh ht
  rw [← hsum, hmain] at he
  have hre := congrArg Complex.re he
  change (fwdDiff h)^[n + 2] (smoothedMangoldt n) t =
    Real.exp t * (Real.exp h - 1) ^ (n + 2) - Z.re + V.re at hre
  have hZre := Complex.re_le_norm Z
  have hVre : -V.re ≤ ‖V‖ := (neg_le_abs V.re).trans (Complex.abs_re_le_norm V)
  have hZ := smoothed_zero_norm_le_occurrences_and_tail n hT hh ht
  have hV := spectralSmoothing_trivialPrimitive_norm_le n hh ht
  change ‖Z‖ ≤ _ at hZ
  change ‖V‖ ≤ _ at hV
  linarith

theorem exists_prime_of_smoothed_total_error (n : ℕ) {T h t : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (herror :
      2 * Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * h ^ (n + 2) *
        (∑ z ∈ zetaZeroOccurrences T,
          Real.exp (-(t + ((n + 2 : ℕ) : ℝ) * h) * (1 - z.1.re))) +
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        (∑' ρ : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) +
      (Real.pi ^ 2 / 6) * h ^ n +
      h ^ (n + 1) * nonprimeMangoldtMass ⌊Real.exp (t + ((n + 2 : ℕ) : ℝ) * h)⌋₊ <
        Real.exp t * (Real.exp h - 1) ^ (n + 2)) :
    ∃ p : ℕ, p.Prime ∧ t ≤ Real.log p ∧ Real.log p ≤ t + ((n + 2 : ℕ) : ℝ) * h := by
  apply exists_prime_of_smoothedMangoldt_bound n hh t
  have hmain := smoothed_detector_lower_estimate n hT hh ht
  linarith

end Sidon
