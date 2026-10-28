module

public import Sidon.NumberTheory.SmoothedMangoldt
public import Sidon.NumberTheory.PrimePowerError

@[expose] public section

/-! Removing the nonprime prime powers from a positive compact detector. -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem exists_prime_of_kernel_mangoldt_bound {N r : ℕ} (hr : 0 < r)
    {h : ℝ} (hh : 0 ≤ h) (t : ℝ)
    (hpos : h ^ (r - 1) * nonprimeMangoldtMass N <
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * primeDetectorKernel r h (t - Real.log n)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ t ≤ Real.log p ∧ Real.log p ≤ t + (r : ℝ) * h := by
  let a : ℕ → ℝ := fun n => if n.Prime then ArithmeticFunction.vonMangoldt n else 0
  let b : ℕ → ℝ := fun n => if n.Prime then 0 else ArithmeticFunction.vonMangoldt n
  have ha : ∀ n ∈ Finset.Icc 1 N, 0 ≤ a n := by
    intro n _
    dsimp [a]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · rfl
  have hb : ∀ n ∈ Finset.Icc 1 N, 0 ≤ b n := by
    intro n _
    dsimp [b]
    split_ifs
    · rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  have hid : (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * primeDetectorKernel r h (t - Real.log n)) =
      (∑ n ∈ Finset.Icc 1 N, a n * primeDetectorKernel r h (t - Real.log n)) +
        ∑ n ∈ Finset.Icc 1 N, b n * primeDetectorKernel r h (t - Real.log n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a, b]
    split_ifs <;> ring
  have hbound := sum_primeDetectorKernel_le (Finset.Icc 1 N) b (fun n => Real.log n) hr hh hb t
  have hbmass : (∑ n ∈ Finset.Icc 1 N, b n) = nonprimeMangoldtMass N := rfl
  rw [hbmass] at hbound
  have hprime : 0 < ∑ n ∈ Finset.Icc 1 N, a n * primeDetectorKernel r h (t - Real.log n) := by
    linarith
  obtain ⟨p, hp, hpa, hlow, hupp⟩ :=
    exists_supported_weight_of_sum_primeDetectorKernel_pos (Finset.Icc 1 N) a
      (fun n => Real.log n) hr hh ha t hprime
  have hpp : p.Prime := by
    by_contra hp'
    simp [a, hp'] at hpa
  exact ⟨p, hpp, (Finset.mem_Icc.mp hp).2, hlow, hupp⟩

theorem exists_prime_of_smoothedMangoldt_bound (j : ℕ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ)
    (hpos : h ^ (j + 1) * nonprimeMangoldtMass
        ⌊Real.exp (t + ((j + 2 : ℕ) : ℝ) * h)⌋₊ <
      (fwdDiff h)^[j + 2] (smoothedMangoldt j) t) :
    ∃ p : ℕ, p.Prime ∧ t ≤ Real.log p ∧ Real.log p ≤ t + ((j + 2 : ℕ) : ℝ) * h := by
  rw [fwdDiff_iter_smoothedMangoldt j hh] at hpos
  have hp := exists_prime_of_kernel_mangoldt_bound (by omega : 0 < j + 2) hh t
    (by simpa only [show j + 2 - 1 = j + 1 by omega] using hpos)
  obtain ⟨p, hprime, _, hl, hu⟩ := hp
  exact ⟨p, hprime, hl, hu⟩


theorem nonprimeMangoldtMass_floor_isLittleO :
    (fun x : ℝ => nonprimeMangoldtMass ⌊x⌋₊) =o[Filter.atTop]
      (fun x : ℝ => x ^ ((2 : ℝ) / 3)) := by
  have hcomp := nonprimeMangoldtMass_isLittleO.comp_tendsto
    (tendsto_nat_floor_atTop : Filter.Tendsto (fun x : ℝ => ⌊x⌋₊) Filter.atTop Filter.atTop)
  apply hcomp.trans_isBigO
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  change ‖(⌊x⌋₊ : ℝ) ^ ((2 : ℝ) / 3)‖ ≤ 1 * ‖x ^ ((2 : ℝ) / 3)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx) (by norm_num)

theorem eventually_nonprimeMangoldtMass_floor_lt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      nonprimeMangoldtMass ⌊x⌋₊ < c * x ^ ((2 : ℝ) / 3) := by
  have hb := nonprimeMangoldtMass_floor_isLittleO.bound (half_pos hc)
  filter_upwards [hb, Filter.eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rw [Real.norm_eq_abs, abs_of_nonneg (nonprimeMangoldtMass_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)] at hx
  have hp := Real.rpow_pos_of_pos hxpos ((2 : ℝ) / 3)
  nlinarith

theorem eventually_nonprimeKernel_error_lt (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (x ^ ((-1 : ℝ) / 3)) ^ n * nonprimeMangoldtMass ⌊x⌋₊ <
        c * x * (x ^ ((-1 : ℝ) / 3)) ^ (n + 1) := by
  filter_upwards [eventually_nonprimeMangoldtMass_floor_lt hc,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hscale : x ^ ((2 : ℝ) / 3) = x * x ^ ((-1 : ℝ) / 3) := by
    calc
      _ = x ^ ((1 : ℝ) + (-1 : ℝ) / 3) := by congr 1; norm_num
      _ = x ^ (1 : ℝ) * x ^ ((-1 : ℝ) / 3) := Real.rpow_add hxpos _ _
      _ = _ := by rw [Real.rpow_one]
  have hmul := mul_lt_mul_of_pos_left hx
    (pow_pos (Real.rpow_pos_of_pos hxpos ((-1 : ℝ) / 3)) n)
  rw [hscale] at hmul
  convert hmul using 1; ring

end Sidon
