module

public import Sidon.NumberTheory.PrimeDetectorParameters
public import Sidon.NumberTheory.ZetaZeroWeight

@[expose] public section

/-! A power-saving prime interval from the actual finite zero-weight limit. -/

noncomputable section

open RiemannGaussian Filter
open scoped Topology

namespace Sidon

theorem eventually_prime_interval_of_zeroWeight_tendsto
    (hweight : Tendsto primeDetectorZeroWeight atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧
      x - 128 * x ^ ((2 : ℝ) / 3) ≤ (p : ℝ) ∧ (p : ℝ) ≤ x := by
  let M : ℝ := ∑' ρ : NontrivialZetaZero,
    (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  have hw := hweight.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hhi := (tendsto_primeDetector_high_ratio M).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hv := tendsto_primeDetector_trivial_ratio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hs : Tendsto (fun x => 128 * primeDetectorStep x) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_primeDetectorStep.const_mul 128
  have hstep := hs.eventually (Iio_mem_nhds
    (lt_min (Real.log_pos (by norm_num : (1 : ℝ) < 2)) zero_lt_one))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hnp := eventually_nonprimeKernel_error_lt 127 (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hw, hhi, hv, hstep, hlog, hnp, eventually_gt_atTop (1 : ℝ)]
    with x hw hhi hv hstep hlog hnp hx1
  have hx : 0 < x := zero_lt_one.trans hx1
  have hh : 0 < primeDetectorStep x := primeDetectorStep_pos hx
  have hT : 0 < primeDetectorHeight x := primeDetectorHeight_pos hx
  have hspos : 0 < primeDetectorScale x := primeDetectorScale_pos hx
  have ht : 0 ≤ primeDetectorTime x := by
    unfold primeDetectorTime
    have hstep1 := hstep.trans_le (min_le_right _ _)
    linarith
  have hmain : primeDetectorScale x / 2 ≤
      Real.exp (primeDetectorTime x) * (Real.exp (primeDetectorStep x) - 1) ^ 128 := by
    calc
      _ = (x / 2) * primeDetectorStep x ^ 128 := by unfold primeDetectorScale; ring
      _ ≤ _ := exponential_mainTerm_lower_bound_at_log 128 hx hh.le
        (hstep.le.trans (min_le_left _ _))
  have hlo : 2 * x * primeDetectorStep x ^ 128 * primeDetectorZeroWeight x <
      primeDetectorScale x / 8 := by
    calc
      _ = (2 * primeDetectorScale x) * primeDetectorZeroWeight x := by unfold primeDetectorScale; ring
      _ < (2 * primeDetectorScale x) * (1 / 16) :=
        mul_lt_mul_of_pos_left hw (by positivity)
      _ = _ := by ring
  have hhibound : (x * 2 ^ 128 / primeDetectorHeight x ^ 126) * M <
      primeDetectorScale x / 16 := by
    rw [primeDetector_high_error_eq hx]
    calc
      _ < primeDetectorScale x * (1 / 16) := mul_lt_mul_of_pos_left hhi hspos
      _ = _ := by ring
  have hvbound : (Real.pi ^ 2 / 6) * primeDetectorStep x ^ 126 <
      primeDetectorScale x / 16 := by
    rw [primeDetector_trivial_error_eq hx]
    calc
      _ < primeDetectorScale x * (1 / 16) := mul_lt_mul_of_pos_left hv hspos
      _ = _ := by ring
  have hnpbound : primeDetectorStep x ^ 127 * nonprimeMangoldtMass ⌊x⌋₊ <
      primeDetectorScale x / 16 := by
    calc
      _ < (1 / 16) * x * primeDetectorStep x ^ 128 := hnp
      _ = _ := by unfold primeDetectorScale; ring
  have herror :
      2 * x * primeDetectorStep x ^ 128 * primeDetectorZeroWeight x +
        (x * 2 ^ 128 / primeDetectorHeight x ^ 126) * M +
        (Real.pi ^ 2 / 6) * primeDetectorStep x ^ 126 +
        primeDetectorStep x ^ 127 * nonprimeMangoldtMass ⌊x⌋₊ <
      Real.exp (primeDetectorTime x) * (Real.exp (primeDetectorStep x) - 1) ^ 128 := by
    linarith
  have hp := exists_prime_of_smoothed_total_error 126 hT hh.le ht (by
    simpa only [show 126 + 2 = 128 from rfl, show 126 + 1 = 127 from rfl,
      Nat.cast_ofNat, primeDetector_window, Real.exp_log hx,
      primeDetectorZeroWeight, primeDetectorHeight] using herror)
  obtain ⟨p, hprime, hlower, hupper⟩ := hp
  have hupper' : Real.log p ≤ Real.log x := by
    simpa only [show 126 + 2 = 128 from rfl, Nat.cast_ofNat, primeDetector_window] using hupper
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hple : (p : ℝ) ≤ x := by
    have hh := Real.exp_le_exp.mpr hupper'
    simpa only [Real.exp_log hp0, Real.exp_log hx] using hh
  have hplower : Real.exp (primeDetectorTime x) ≤ (p : ℝ) := by
    simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hlower
  have hnear : x - 128 * x ^ ((2 : ℝ) / 3) ≤ Real.exp (primeDetectorTime x) := by
    have he := Real.add_one_le_exp (-128 * primeDetectorStep x)
    have hm := mul_le_mul_of_nonneg_left he hx.le
    have hexp : Real.exp (primeDetectorTime x) = x * Real.exp (-128 * primeDetectorStep x) := by
      unfold primeDetectorTime
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx]
      simp only [neg_mul]
    rw [hexp]
    have hxs := mul_primeDetectorStep_eq hx
    nlinarith
  exact ⟨p, hprime, hnear.trans hplower, hple⟩

theorem eventually_prime_interval_of_uniform_zero_density
    {A K T₀ : ℝ} {B : ℕ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hAupper : A < 50 / 17)
    (hdensity : UniformZetaZeroDensity A B K T₀) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧
      x - 128 * x ^ ((2 : ℝ) / 3) ≤ (p : ℝ) ∧ (p : ℝ) ≤ x := by
  apply eventually_prime_interval_of_zeroWeight_tendsto
  unfold primeDetectorZeroWeight primeDetectorHeight
  exact tendsto_zetaZeroWeight_seventeen_fiftieths_of_density hA hK hAupper hdensity

end Sidon
