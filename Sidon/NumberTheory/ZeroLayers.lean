import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Finite layer bounds for zero-density arguments -/

noncomputable section

namespace Sidon

variable {ι : Type*}

theorem geometric_sum_Ico_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r J : ℕ) :
    (∑ j ∈ Finset.Ico r J, q ^ j) ≤ q ^ r / (1 - q) := by
  by_cases hrJ : r ≤ J
  · rw [geom_sum_Ico hq1.ne hrJ]
    have heq : (q ^ J - q ^ r) / (q - 1) = (q ^ r - q ^ J) / (1 - q) := by
      rw [show q - 1 = -(1 - q) by ring, div_neg, ← neg_div, neg_sub]
    rw [heq]
    exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hq0 J)) (by linarith)
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    exact div_nonneg (pow_nonneg hq0 r) (by linarith)

/-- Exponential growth of layer sizes is dominated by faster decay of the weights. -/
theorem sum_layer_weights_le (s : Finset ι) (k : ι → ℕ) (w : ι → ℝ)
    {K a b : ℝ} (hK : 0 ≤ K) (hba : b < a) (r : ℕ)
    (hkr : ∀ i ∈ s, r ≤ k i)
    (hw : ∀ i ∈ s, w i ≤ Real.exp (-a * k i))
    (hcount : ∀ j : ℕ, ((s.filter (fun i => k i = j)).card : ℝ) ≤ K * Real.exp (b * j)) :
    (∑ i ∈ s, w i) ≤ K * Real.exp (-(a - b) * r) / (1 - Real.exp (-(a - b))) := by
  classical
  let J := max r ((s.image k).sup id + 1)
  have hmaps (i : ι) (hi : i ∈ s) : k i ∈ Finset.Ico r J := by
    apply Finset.mem_Ico.mpr
    refine ⟨hkr i hi, ?_⟩
    have hh : k i ≤ (s.image k).sup id := Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    dsimp [J]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  have hq0 : 0 ≤ Real.exp (-(a - b)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(a - b)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc
    _ ≤ ∑ j ∈ Finset.Ico r J, (K * Real.exp (b * j)) * Real.exp (-a * j) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _i ∈ s.filter (fun i => k i = j), Real.exp (-a * j) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
          simpa only [hij] using hw i his
        _ = ((s.filter (fun i => k i = j)).card : ℝ) * Real.exp (-a * j) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount j) (Real.exp_pos _).le
    _ = K * ∑ j ∈ Finset.Ico r J, (Real.exp (-(a - b))) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ K * (Real.exp (-(a - b))) ^ r / (1 - Real.exp (-(a - b))) := by
      have hh := mul_le_mul_of_nonneg_left (geometric_sum_Ico_le hq0 hq1 r J) hK
      simpa only [mul_div_assoc] using hh
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

def zeroLayer (s : Finset ι) (β : ι → ℝ) (L : ℝ) (j : ℕ) : Finset ι :=
  s.filter fun i => Nat.floor (L * (1 - β i)) = j

/-- A finite zero-free region removes the initial density layers. -/
theorem finite_zero_layer_bound (s : Finset ι) (β : ι → ℝ)
    {L η K b : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hb : b < 1)
    (hβ : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ j : ℕ, ((zeroLayer s β L j).card : ℝ) ≤ K * Real.exp (b * (j + 1))) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp b) * Real.exp (-(1 - b) * Nat.floor (L * η)) /
        (1 - Real.exp (-(1 - b))) := by
  classical
  let k := fun i => Nat.floor (L * (1 - β i))
  apply sum_layer_weights_le s k (fun i => Real.exp (-L * (1 - β i)))
    (mul_nonneg hK (Real.exp_pos b).le) hb (Nat.floor (L * η))
  · intro i hi
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith [hβ i hi]) hL.le)
  · intro i hi
    have hdist : 0 ≤ L * (1 - β i) := mul_nonneg hL.le (by linarith [hβ i hi])
    apply Real.exp_le_exp.mpr
    have hfloor := Nat.floor_le hdist
    change -L * (1 - β i) ≤ -(1 : ℝ) * (k i : ℝ)
    dsimp [k]
    linarith
  · intro j
    have h := hcount j
    change ((zeroLayer s β L j).card : ℝ) ≤ _
    convert h using 1
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring

end Sidon
