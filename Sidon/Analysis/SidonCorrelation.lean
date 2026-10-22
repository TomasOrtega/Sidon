import Sidon.Analysis.VanDerCorput
import Sidon.Combinatorics.IntervalSize
import Mathlib.Tactic

/-! # Correlation estimates for a Sidon set and its interval model -/

noncomputable section

open scoped ComplexConjugate

namespace Sidon

def intervalModel (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  ((S.card : ℝ) / N) • indicatorFinsupp (interval N)

def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)

def boundaryPart (N : ℕ) (S : Finset ℤ) (h : ℤ) : Finset ℤ :=
  S.filter fun x => x + h ∉ interval N

theorem correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    correlation (indicatorFinsupp S) (indicatorFinsupp T) h =
      (((S.filter fun x => x + h ∈ T).card : ℕ) : ℂ) := by
  classical
  rw [correlation, Finsupp.sum, support_indicatorFinsupp, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp [indicatorFinsupp_apply, hx]

theorem re_correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).re =
      ((S.filter fun x => x + h ∈ T).card : ℝ) := by
  rw [correlation_indicatorFinsupp]
  simp

theorem im_correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).im = 0 := by
  rw [correlation_indicatorFinsupp]
  simp

theorem re_correlation_indicatorFinsupp_zero (S : Finset ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp S) 0).re = S.card := by
  rw [re_correlation_indicatorFinsupp]
  simp only [add_zero]
  rw [Finset.filter_eq_self.mpr (fun _ hx => hx)]

theorem re_correlation_indicatorFinsupp_nonneg (S T : Finset ℤ) (h : ℤ) :
    0 ≤ (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).re := by
  rw [re_correlation_indicatorFinsupp]
  positivity

theorem re_correlation_indicatorFinsupp_le_one {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) {h : ℤ} (hh : h ≠ 0) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re ≤ 1 := by
  rw [re_correlation_indicatorFinsupp]
  have hcard : (S.filter fun x => x + h ∈ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hyh⟩ := Finset.mem_filter.mp hy
    exact (hS.eq_of_sub_eq_sub hxh hx hyh hy (by omega) (by omega)).2
  exact_mod_cast hcard

theorem boundaryPart_card_add (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (S.filter fun x => x + h ∈ interval N).card + (boundaryPart N S h).card =
      S.card := by
  exact Finset.card_filter_add_card_filter_not _

theorem re_correlation_intervalModel_right (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (intervalModel N S) h).re =
      ((S.card : ℝ) / N) * ((S.filter fun x => x + h ∈ interval N).card : ℝ) := by
  rw [intervalModel, correlation_real_smul_right, Complex.smul_re,
    re_correlation_indicatorFinsupp]
  rfl

theorem intervalModel_mixed_deficit (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    |(S.card : ℝ) ^ 2 / N -
        (correlation (indicatorFinsupp S) (intervalModel N S) h).re| =
      ((S.card : ℝ) / N) * (boundaryPart N S h).card := by
  rw [re_correlation_intervalModel_right]
  have hcard : ((S.filter fun x => x + h ∈ interval N).card : ℝ) +
      (boundaryPart N S h).card = (S.card : ℝ) := by
    exact_mod_cast boundaryPart_card_add N S h
  have hnonneg : 0 ≤ ((S.card : ℝ) / N) * (boundaryPart N S h).card := by positivity
  have heq : (S.card : ℝ) ^ 2 / N -
      ((S.card : ℝ) / N) * ((S.filter fun x => x + h ∈ interval N).card : ℝ) =
      ((S.card : ℝ) / N) * (boundaryPart N S h).card := by
    rw [← hcard]
    ring
  rw [heq, abs_of_nonneg hnonneg]

theorem boundaryPart_card_le {N : ℕ} {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (h : ℤ) :
    ((boundaryPart N S h).card : ℝ) ≤ 2 * Real.sqrt |(h : ℝ)| := by
  have hB : IsSidonSet ((boundaryPart N S h : Finset ℤ) : Set ℤ) :=
    hS.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have habs : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← habs]
  by_cases hh : 0 ≤ h
  · apply hB.card_le_two_mul_sqrt_of_subset_Icc ((N : ℤ) - h)
    intro x hx
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
    have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
    have hnat : (h.natAbs : ℤ) = h := by
      rw [Int.natCast_natAbs, abs_of_nonneg hh]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · apply hB.card_le_two_mul_sqrt_of_subset_Icc 0
    intro x hx
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
    have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
    have hnat : (h.natAbs : ℤ) = -h := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hh)]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem correlationError_swap (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) :
    correlationError N S H g f = correlationError N S H f g := by
  unfold correlationError
  simp only [correlation_swap_neg f g, Complex.conj_re]
  exact sum_fejerWeight_mul_neg H
    (fun h => |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)

theorem mixed_correlationError_le {N H : ℕ} {S : Finset ℤ}
    (hH : 0 < H) (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    correlationError N S H (indicatorFinsupp S) (intervalModel N S) ≤
      2 * (S.card : ℝ) * Real.sqrt H / N := by
  unfold correlationError
  apply sum_fejerWeight_mul_le H hH
  intro h hh
  rw [intervalModel_mixed_deficit]
  have hbound := boundaryPart_card_le hS hSN h
  have habs : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (abs_lt_of_mem_support_fejerWeight H hh).le
  have hsqrt := Real.sqrt_le_sqrt habs
  have hcoeff : 0 ≤ (S.card : ℝ) / N := by positivity
  calc
    ((S.card : ℝ) / N) * (boundaryPart N S h).card ≤
        ((S.card : ℝ) / N) * (2 * Real.sqrt |(h : ℝ)|) :=
      mul_le_mul_of_nonneg_left hbound hcoeff
    _ ≤ ((S.card : ℝ) / N) * (2 * Real.sqrt H) := by gcongr
    _ = 2 * (S.card : ℝ) * Real.sqrt H / N := by ring

theorem interval_overlap_card {N : ℕ} {h : ℤ} (hh : |h| ≤ (N : ℤ)) :
    (((interval N).filter fun x => x + h ∈ interval N).card : ℝ) =
      (N : ℝ) - |(h : ℝ)| := by
  classical
  have hh' := abs_le.mp hh
  by_cases hh₀ : 0 ≤ h
  · have hset : ((interval N).filter fun x => x + h ∈ interval N) =
        Finset.Icc 1 ((N : ℤ) - h) := by
      ext x
      simp only [Finset.mem_filter, mem_interval, Finset.mem_Icc]
      omega
    rw [hset]
    have hcast : ((Finset.Icc 1 ((N : ℤ) - h)).card : ℤ) = (N : ℤ) - h := by
      calc
        _ = ((N : ℤ) - h) + 1 - 1 := Int.card_Icc_of_le 1 ((N : ℤ) - h) (by omega)
        _ = _ := by omega
    have hreal : ((Finset.Icc 1 ((N : ℤ) - h)).card : ℝ) = (N : ℝ) - h := by
      exact_mod_cast hcast
    rw [hreal, abs_of_nonneg (show (0 : ℝ) ≤ h by exact_mod_cast hh₀)]
  · have hset : ((interval N).filter fun x => x + h ∈ interval N) =
        Finset.Icc (1 - h) (N : ℤ) := by
      ext x
      simp only [Finset.mem_filter, mem_interval, Finset.mem_Icc]
      omega
    rw [hset]
    have hcast : ((Finset.Icc (1 - h) (N : ℤ)).card : ℤ) = (N : ℤ) + h := by
      calc
        _ = (N : ℤ) + 1 - (1 - h) := Int.card_Icc_of_le (1 - h) (N : ℤ) (by omega)
        _ = _ := by omega
    have hreal : ((Finset.Icc (1 - h) (N : ℤ)).card : ℝ) = (N : ℝ) + h := by
      exact_mod_cast hcast
    rw [hreal, abs_of_neg (show (h : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hh₀))]
    ring

theorem re_correlation_intervalModel_self (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (correlation (intervalModel N S) (intervalModel N S) h).re =
      ((S.card : ℝ) / N) ^ 2 *
        (((interval N).filter fun x => x + h ∈ interval N).card : ℝ) := by
  rw [intervalModel, correlation_real_smul_left, correlation_real_smul_right,
    Complex.smul_re, Complex.smul_re, re_correlation_indicatorFinsupp]
  simp only [smul_eq_mul]
  ring

theorem intervalModel_self_deficit {N : ℕ} (hN : 0 < N) (S : Finset ℤ)
    {h : ℤ} (hh : |h| ≤ (N : ℤ)) :
    |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (intervalModel N S) h).re| =
      (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| := by
  rw [re_correlation_intervalModel_self, interval_overlap_card hh]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have heq : (S.card : ℝ) ^ 2 / N - ((S.card : ℝ) / N) ^ 2 *
      ((N : ℝ) - |(h : ℝ)|) = (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]

theorem intervalModel_correlationError_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hHN : H ≤ N) (S : Finset ℤ) :
    correlationError N S H (intervalModel N S) (intervalModel N S) ≤
      (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 := by
  unfold correlationError
  apply sum_fejerWeight_mul_le H hH
  intro h hh
  have habs : |h| ≤ (N : ℤ) := by
    have := abs_lt_of_mem_support_fejerWeight H hh
    exact le_trans this.le (by exact_mod_cast hHN)
  rw [intervalModel_self_deficit hN S habs]
  have hh' : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (abs_lt_of_mem_support_fejerWeight H hh).le
  calc
    (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| ≤
        (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * H := by gcongr
    _ = (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 := by ring

theorem self_correlation_mass_ge {N H : ℕ} (hH : 0 < H) (S : Finset ℤ)
    (hSN : S ⊆ interval N) :
    (S.card : ℝ) ^ 2 / ((N : ℝ) + H) ≤
      (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) := by
  have hsum : (indicatorFinsupp S).sum (fun _ c => c) = (S.card : ℂ) := by
    rw [← fourierSum_apply_zero, fourierSum_indicatorFinsupp_zero]
  have hv := vanDerCorput_norm N H hH (indicatorFinsupp S)
    (by simpa only [support_indicatorFinsupp] using hSN)
  rw [hsum] at hv
  have hv' : (S.card : ℝ) ^ 2 ≤ ((N : ℝ) + H) *
      (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) := by
    simpa using hv
  apply (div_le_iff₀ (show (0 : ℝ) < (N : ℝ) + H by positivity)).mpr
  simpa only [mul_comm] using hv'

theorem self_correlation_pointwise_error {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (b : ℝ) (h : ℤ) :
    |b - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| ≤
      (1 + |b - 1|) - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re +
        if h = 0 then 2 * (S.card : ℝ) else 0 := by
  by_cases hh : h = 0
  · subst h
    rw [re_correlation_indicatorFinsupp_zero, if_pos rfl]
    apply abs_le.mpr
    constructor <;> nlinarith [le_abs_self (b - 1), neg_le_abs (b - 1),
      Nat.cast_nonneg (α := ℝ) S.card]
  · rw [if_neg hh, add_zero]
    have hr := re_correlation_indicatorFinsupp_le_one hS hh
    calc
      |b - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| =
          |(b - 1) + (1 -
            (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re)| := by
        congr 1
        ring
      _ ≤ |b - 1| + |1 -
          (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hr)]; ring

theorem self_correlationError_le_mass {N H : ℕ} (hH : 0 < H) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) :
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
      1 - (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
      |(S.card : ℝ) ^ 2 / N - 1| + 2 * (S.card : ℝ) / H := by
  let b : ℝ := (S.card : ℝ) ^ 2 / N
  let m : ℝ := S.card
  have hzero : 0 ∈ (fejerWeight H).support := by
    rw [Finsupp.mem_support_iff, fejerWeight_zero H hH]
    positivity
  have hdelta : (fejerWeight H).sum
      (fun h w => w * (if h = 0 then 2 * m else 0)) = 2 * m / H := by
    simp only [mul_ite, mul_zero, Finsupp.sum]
    rw [Finset.sum_ite_eq']
    simp only [hzero, if_true, fejerWeight_zero H hH]
    ring
  calc
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
        (fejerWeight H).sum (fun h w => w * ((1 + |b - 1|) -
          (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re +
            if h = 0 then 2 * m else 0)) := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left (self_correlation_pointwise_error hS b h)
        (fejerWeight_nonneg H h)
    _ = (1 + |b - 1|) * (fejerWeight H).sum (fun _ w => w) -
        (fejerWeight H).sum (fun h w =>
          w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
        (fejerWeight H).sum (fun h w => w * (if h = 0 then 2 * m else 0)) := by
      simp only [Finsupp.sum, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = _ := by rw [sum_fejerWeight H hH, hdelta]; dsimp only [b, m]; ring

theorem self_correlationError_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
      2 * |(S.card : ℝ) ^ 2 / N - 1| +
        (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 + 2 * (S.card : ℝ) / H := by
  have hmass := self_correlation_mass_ge hH S hSN
  have herror := self_correlationError_le_mass (N := N) hH hS
  have hN' : (0 : ℝ) < N := by positivity
  have hNH : (N : ℝ) + H ≠ 0 := by positivity
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN'
  have hid : 1 - (S.card : ℝ) ^ 2 / ((N : ℝ) + H) =
      1 - (S.card : ℝ) ^ 2 / N +
        ((S.card : ℝ) ^ 2 / N * H) / ((N : ℝ) + H) := by
    field_simp
    ring
  have hsmall : ((S.card : ℝ) ^ 2 / N * H) / ((N : ℝ) + H) ≤
      ((S.card : ℝ) ^ 2 / N * H) / N := by
    apply div_le_div_of_nonneg_left (by positivity) hN'
    linarith [Nat.cast_nonneg (α := ℝ) H]
  have hrew : ((S.card : ℝ) ^ 2 / N * H) / N =
      (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 := by ring
  have habs : 1 - (S.card : ℝ) ^ 2 / N ≤ |(S.card : ℝ) ^ 2 / N - 1| := by
    linarith [neg_le_abs ((S.card : ℝ) ^ 2 / N - 1)]
  rw [hrew] at hsmall
  linarith

end Sidon
