import Sidon.Combinatorics.SharpIntervalSize

/-! # Finite window counts and their variance -/

noncomputable section

namespace Sidon

def windowSum (H : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  ∑ u ∈ Finset.range H, integerShift (-(u : ℤ)) (indicatorFinsupp S)

def windowCount (H : ℕ) (S : Finset ℤ) (t : ℤ) : ℝ := (windowSum H S t).re

def sidonDeficit (N : ℕ) (S : Finset ℤ) : ℝ :=
  max 0 (1 - (S.card : ℝ) / Real.sqrt N)

/-- One zero window pads the natural interval of backward window counts. -/
def windowVariance (N H : ℕ) (S : Finset ℤ) : ℝ :=
  ∑ t ∈ interval (N + H),
    (windowCount H S t - (H : ℝ) * S.card / (N + H : ℕ)) ^ 2

theorem indicatorFinsupp_eq_sum_single (S : Finset ℤ) :
    indicatorFinsupp S = ∑ s ∈ S, Finsupp.single s (1 : ℂ) := by
  classical
  ext x
  simp only [indicatorFinsupp_apply, Finset.sum_apply', Finsupp.single_apply,
    Finset.sum_ite_eq']

theorem windowSum_apply (H : ℕ) (S : Finset ℤ) (t : ℤ) :
    windowSum H S t = ∑ s ∈ S, ∑ u ∈ Finset.range H,
      if s + (u : ℤ) = t then (1 : ℂ) else 0 := by
  classical
  rw [windowSum, indicatorFinsupp_eq_sum_single]
  simp only [integerShift, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    sub_neg_eq_add, Finset.sum_apply', Finsupp.single_apply]
  exact Finset.sum_comm

theorem windowCount_apply (H : ℕ) (S : Finset ℤ) (t : ℤ) :
    windowCount H S t = ∑ s ∈ S, ∑ u ∈ Finset.range H,
      if s + (u : ℤ) = t then (1 : ℝ) else 0 := by
  simp [windowCount, windowSum_apply]

theorem windowSum_im (H : ℕ) (S : Finset ℤ) (t : ℤ) : (windowSum H S t).im = 0 := by
  simp [windowSum_apply]

theorem windowCount_nonneg (H : ℕ) (S : Finset ℤ) (t : ℤ) : 0 ≤ windowCount H S t := by
  rw [windowCount_apply]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem support_windowSum_subset {N : ℕ} (H : ℕ) (S : Finset ℤ)
    (hSN : S ⊆ interval N) : (windowSum H S).support ⊆ interval (N + H) := by
  classical
  intro t ht
  by_contra hnot
  apply Finsupp.mem_support_iff.mp ht
  rw [windowSum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro u hu
  rw [if_neg]
  intro heq
  have hs' := mem_interval.mp (hSN hs)
  have hu' := Finset.mem_range.mp hu
  apply hnot
  apply mem_interval.mpr
  constructor <;> omega

theorem sum_windowCount (H : ℕ) (S U : Finset ℤ) :
    ∑ t ∈ U, windowCount H S t =
      ∑ s ∈ S, ∑ u ∈ Finset.range H,
        if s + (u : ℤ) ∈ U then (1 : ℝ) else 0 := by
  classical
  simp_rw [windowCount_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]

theorem sum_windowCount_interval {N : ℕ} (H : ℕ) (S : Finset ℤ)
    (hSN : S ⊆ interval N) :
    ∑ t ∈ interval (N + H), windowCount H S t = (H : ℝ) * S.card := by
  rw [sum_windowCount]
  have hall : ∀ s ∈ S, ∀ u ∈ Finset.range H, s + (u : ℤ) ∈ interval (N + H) := by
    intro s hs u hu
    have hs' := mem_interval.mp (hSN hs)
    have hu' := Finset.mem_range.mp hu
    exact mem_interval.mpr ⟨by omega, by omega⟩
  calc
    (∑ s ∈ S, ∑ u ∈ Finset.range H,
        if s + (u : ℤ) ∈ interval (N + H) then (1 : ℝ) else 0) =
        ∑ _s ∈ S, ∑ _u ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_congr rfl fun u hu => if_pos (hall s hs u hu)
    _ = _ := by simp [mul_comm]

theorem sum_windowCount_ge_card (H : ℕ) (S U : Finset ℤ) (P : ℤ → Prop)
    [DecidablePred P]
    (hall : ∀ s ∈ S, P s → ∀ u ∈ Finset.range H, s + (u : ℤ) ∈ U) :
    (H : ℝ) * (S.filter P).card ≤ ∑ t ∈ U, windowCount H S t := by
  classical
  rw [sum_windowCount, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  by_cases hP : P s
  · rw [if_pos hP, mul_one]
    have heq : (∑ u ∈ Finset.range H,
        if s + (u : ℤ) ∈ U then (1 : ℝ) else 0) = H := by
      calc
        _ = ∑ _u ∈ Finset.range H, (1 : ℝ) :=
          Finset.sum_congr rfl (fun u hu => if_pos (hall s hs hP u hu))
        _ = _ := by simp
    exact heq.ge
  · rw [if_neg hP, mul_zero]
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem sum_windowCount_le_card (H : ℕ) (S U : Finset ℤ) (P : ℤ → Prop)
    [DecidablePred P]
    (hall : ∀ s ∈ S, ∀ u ∈ Finset.range H, s + (u : ℤ) ∈ U → P s) :
    (∑ t ∈ U, windowCount H S t) ≤ (H : ℝ) * (S.filter P).card := by
  classical
  rw [sum_windowCount, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  by_cases hP : P s
  · rw [if_pos hP, mul_one]
    calc
      (∑ u ∈ Finset.range H, if s + (u : ℤ) ∈ U then (1 : ℝ) else 0) ≤
          ∑ _u ∈ Finset.range H, (1 : ℝ) := by
        exact Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = H := by simp
  · rw [if_neg hP, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro u hu
    exact if_neg (fun hmem => hP (hall s hs u hu hmem))

theorem sum_sq_windowCount {N H : ℕ} (hH : 0 < H) (S : Finset ℤ)
    (hSN : S ⊆ interval N) :
    ∑ t ∈ interval (N + H), windowCount H S t ^ 2 =
      (H : ℝ) ^ 2 * (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) := by
  have henergy : ∑ t ∈ interval (N + H), windowCount H S t ^ 2 =
      (correlation (windowSum H S) (windowSum H S) 0).re := by
    rw [re_correlation_self_zero]
    symm
    apply (Finset.sum_subset (support_windowSum_subset H S hSN) ?_).trans
    · apply Finset.sum_congr rfl
      intro t _
      simp only [Complex.normSq_apply, windowSum_im, pow_two, mul_zero, add_zero, windowCount]
    · intro t _ ht
      change Complex.normSq (windowSum H S t) = 0
      rw [Finsupp.notMem_support_iff.mp ht, Complex.normSq_zero]
  rw [henergy, windowSum, correlation_sum_left]
  simp_rw [correlation_sum_right, correlation_integerShift]
  simp only [Complex.re_sum]
  have harg : ∀ u v : ℕ, (0 : ℤ) + -(v : ℤ) - -(u : ℤ) = (u : ℤ) - v := by
    intro u v
    omega
  simp_rw [harg]
  rw [sum_fejerWeight_mul, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  have hH' : (H : ℝ) ^ 2 ≠ 0 := by positivity
  simp only [mul_inv_cancel₀ hH', one_mul]
  exact Finset.sum_comm

theorem windowVariance_nonneg (N H : ℕ) (S : Finset ℤ) :
    0 ≤ windowVariance N H S := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem windowVariance_eq {N H : ℕ} (hH : 0 < H) (S : Finset ℤ)
    (hSN : S ⊆ interval N) :
    windowVariance N H S =
      (H : ℝ) ^ 2 * (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) -
        (H : ℝ) ^ 2 * (S.card : ℝ) ^ 2 / (N + H : ℕ) := by
  let v : ℝ := (H : ℝ) * S.card / (N + H : ℕ)
  have hNH : ((N + H : ℕ) : ℝ) ≠ 0 := by positivity
  have hexpand : windowVariance N H S =
      (∑ t ∈ interval (N + H), windowCount H S t ^ 2) -
        2 * v * (∑ t ∈ interval (N + H), windowCount H S t) +
        ((N + H : ℕ) : ℝ) * v ^ 2 := by
    unfold windowVariance
    change (∑ t ∈ interval (N + H), (windowCount H S t - v) ^ 2) = _
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      card_interval, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hexpand, sum_sq_windowCount hH S hSN, sum_windowCount_interval H S hSN]
  dsimp only [v]
  field_simp
  ring

theorem deficit_nonneg (N : ℕ) (S : Finset ℤ) : 0 ≤ sidonDeficit N S := le_max_left _ _

theorem square_deficit_le {N : ℕ} (hN : 0 < N) (S : Finset ℤ) :
    (N : ℝ) - (S.card : ℝ) ^ 2 ≤ 2 * (N : ℝ) * sidonDeficit N S := by
  have hNr : (0 : ℝ) < N := by positivity
  have hdiv : (S.card : ℝ) ^ 2 / N = ((S.card : ℝ) / Real.sqrt N) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hNr.le]
  have hmax : 1 - (S.card : ℝ) / Real.sqrt N ≤ sidonDeficit N S := le_max_right _ _
  have hq : 1 - ((S.card : ℝ) / Real.sqrt N) ^ 2 ≤ 2 * sidonDeficit N S := by
    nlinarith [sq_nonneg ((S.card : ℝ) / Real.sqrt N - 1)]
  rw [← hdiv] at hq
  have hmul := mul_le_mul_of_nonneg_left hq hNr.le
  have hcancel : (N : ℝ) * ((S.card : ℝ) ^ 2 / N) = (S.card : ℝ) ^ 2 := by
    field_simp
  nlinarith

theorem sidon_windowVariance_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    windowVariance N H S ≤
      2 * (H : ℝ) ^ 2 * sidonDeficit N S + (H : ℝ) ^ 3 / N +
        5 * (H : ℝ) * Real.sqrt N := by
  have hNr : (0 : ℝ) < N := by positivity
  have hHr : (0 : ℝ) < H := by positivity
  have hNHeq : ((N + H : ℕ) : ℝ) = (N : ℝ) + H := by norm_cast
  have hT : (0 : ℝ) < (N : ℝ) + H := by positivity
  have hupper := weighted_indicator_self_correlation_le hH hS
  have hupper' := mul_le_mul_of_nonneg_left hupper (sq_nonneg (H : ℝ))
  have hm := hS.card_le_five_mul_sqrt hSN
  have hmass : (H : ℝ) * S.card ≤ 5 * (H : ℝ) * Real.sqrt N := by
    nlinarith [mul_le_mul_of_nonneg_left hm hHr.le]
  have hdef := square_deficit_le hN S
  have hdef₀ := deficit_nonneg N S
  have hfrac : 1 - (S.card : ℝ) ^ 2 / ((N : ℝ) + H) ≤
      2 * sidonDeficit N S + (H : ℝ) / N := by
    calc
      1 - (S.card : ℝ) ^ 2 / ((N : ℝ) + H) =
          ((N : ℝ) - (S.card : ℝ) ^ 2 + H) / ((N : ℝ) + H) := by
        field_simp
        ring
      _ ≤ (2 * (N : ℝ) * sidonDeficit N S + H) / ((N : ℝ) + H) := by
        apply div_le_div_of_nonneg_right _ hT.le
        linarith
      _ ≤ (2 * (N : ℝ) * sidonDeficit N S + H) / N :=
        div_le_div_of_nonneg_left (by positivity) hNr (by linarith)
      _ = _ := by field_simp
  have hfrac' := mul_le_mul_of_nonneg_left hfrac (sq_nonneg (H : ℝ))
  rw [windowVariance_eq hH S hSN, hNHeq]
  have hmul : (H : ℝ) ^ 2 * ((S.card : ℝ) / H) = (H : ℝ) * S.card := by
    field_simp
  have hident : (H : ℝ) ^ 2 * ((H : ℝ) / N) = (H : ℝ) ^ 3 / N := by ring
  rw [mul_add, hmul] at hupper'
  rw [mul_add, hident] at hfrac'
  have hfrac'' : (H : ℝ) ^ 2 - (H : ℝ) ^ 2 * (S.card : ℝ) ^ 2 /
      ((N : ℝ) + H) ≤ 2 * (H : ℝ) ^ 2 * sidonDeficit N S + (H : ℝ) ^ 3 / N := by
    convert hfrac' using 1 <;> ring
  linarith only [hupper', hfrac'', hmass]

theorem abs_sum_windowCount_sub_le {N H : ℕ} (S U : Finset ℤ)
    (hU : U ⊆ interval (N + H)) :
    |∑ t ∈ U, (windowCount H S t - (H : ℝ) * S.card / (N + H : ℕ))| ≤
      Real.sqrt U.card * Real.sqrt (windowVariance N H S) := by
  let d : ℤ → ℝ := fun t => windowCount H S t - (H : ℝ) * S.card / (N + H : ℕ)
  have hcs : (∑ t ∈ U, d t) ^ 2 ≤ (U.card : ℝ) * ∑ t ∈ U, d t ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) d
  have hsub : (∑ t ∈ U, d t ^ 2) ≤ windowVariance N H S :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => sq_nonneg _)
  have hle : (∑ t ∈ U, d t) ^ 2 ≤ (U.card : ℝ) * windowVariance N H S :=
    hcs.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _))
  have hsq : (Real.sqrt U.card * Real.sqrt (windowVariance N H S)) ^ 2 =
      (U.card : ℝ) * windowVariance N H S := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (windowVariance_nonneg N H S)]
  have hle' : (∑ t ∈ U, d t) ^ 2 ≤
      (Real.sqrt U.card * Real.sqrt (windowVariance N H S)) ^ 2 := by
    rw [hsq]
    exact hle
  simpa only [abs_of_nonneg (by positivity :
    0 ≤ Real.sqrt U.card * Real.sqrt (windowVariance N H S))] using sq_le_sq.mp hle'

end Sidon
