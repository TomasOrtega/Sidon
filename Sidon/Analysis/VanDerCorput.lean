module

public import Sidon.Analysis.Correlation
public import Sidon.Analysis.DiscreteFejer
public import Sidon.Combinatorics.Intervals

@[expose] public section

/-! # Van der Corput differencing for finite integer functions -/

noncomputable section

namespace Sidon

/-- An average of `H` consecutive translates, starting at displacement zero. -/
def movingAverage (H : ℕ) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  (H : ℝ)⁻¹ • ∑ u ∈ Finset.range H, integerShift (u : ℤ) f

theorem movingAverage_apply (H : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    movingAverage H f x = (H : ℝ)⁻¹ • ∑ u ∈ Finset.range H, f (x + u) := by
  simp only [movingAverage, Finsupp.smul_apply, Finset.sum_apply', integerShift_apply]

private theorem sum_real_smul (c : ℝ) (f : ℤ →₀ ℂ) :
    (c • f).sum (fun _ a => a) = c • f.sum (fun _ a => a) := by
  rw [Finsupp.sum_smul_index' (h := fun _ a => a) (fun _ => rfl)]
  exact (Finset.smul_sum ..).symm

theorem sum_movingAverage (H : ℕ) (hH : 0 < H) (f : ℤ →₀ ℂ) :
    (movingAverage H f).sum (fun _ a => a) = f.sum (fun _ a => a) := by
  rw [movingAverage, sum_real_smul,
    ← Finsupp.sum_finsetSum_index (h := fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [sum_integerShift, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have h : (H : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hH
  rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem support_movingAverage_subset (N H : ℕ) (f : ℤ →₀ ℂ)
    (hf : f.support ⊆ interval N) :
    (movingAverage H f).support ⊆ Finset.Icc (1 - (H : ℤ)) N := by
  intro x hx
  have hxne : movingAverage H f x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hex : ∃ u ∈ Finset.range H, f (x + u) ≠ 0 := by
    by_contra! h
    apply hxne
    rw [movingAverage_apply, Finset.sum_eq_zero (fun u hu => h u hu), smul_zero]
  obtain ⟨u, hu, hfu⟩ := hex
  have hxrange := mem_interval.mp (hf (Finsupp.mem_support_iff.mpr hfu))
  have huH := Finset.mem_range.mp hu
  apply Finset.mem_Icc.mpr
  constructor <;> omega

theorem correlation_movingAverage (H : ℕ) (f g : ℤ →₀ ℂ) :
    correlation (movingAverage H f) (movingAverage H g) 0 =
      (fejerWeight H).sum (fun h w => w • correlation f g h) := by
  rw [movingAverage, movingAverage, correlation_real_smul_left, correlation_real_smul_right,
    correlation_sum_left, sum_fejerWeight_smul]
  simp_rw [correlation_sum_right, correlation_integerShift, zero_add]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  simp [pow_two, mul_inv]

theorem re_correlation_movingAverage (H : ℕ) (f : ℤ →₀ ℂ) :
    (correlation (movingAverage H f) (movingAverage H f) 0).re =
      (fejerWeight H).sum (fun h w => w * (correlation f f h).re) := by
  rw [correlation_movingAverage]
  simp [Finsupp.sum, Complex.real_smul]

theorem weighted_re_correlation_nonneg (H : ℕ) (f : ℤ →₀ ℂ) :
    0 ≤ (fejerWeight H).sum (fun h w => w * (correlation f f h).re) := by
  rw [← re_correlation_movingAverage]
  exact re_correlation_self_zero_nonneg _

theorem weighted_correlation_im (H : ℕ) (f : ℤ →₀ ℂ) :
    ((fejerWeight H).sum (fun h w => w • correlation f f h)).im = 0 := by
  rw [← correlation_movingAverage, correlation_self_zero]
  simp [Finsupp.sum]

theorem normSq_sum_le_card_mul {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, z i) ≤ (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (z i) := by
  have hre : (∑ i ∈ s, (z i).re) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (z i).re ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (z i).re)
  have him : (∑ i ∈ s, (z i).im) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (z i).im ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (z i).im)
  calc
    Complex.normSq (∑ i ∈ s, z i) =
        (∑ i ∈ s, (z i).re) ^ 2 + (∑ i ∈ s, (z i).im) ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (z i).re ^ 2 +
        (s.card : ℝ) * ∑ i ∈ s, (z i).im ^ 2 := add_le_add hre him
    _ = (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (z i) := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [Complex.normSq_apply, pow_two]

theorem finsupp_normSq_sum_le_card_mul (s : Finset ℤ) (f : ℤ →₀ ℂ)
    (hf : f.support ⊆ s) :
    Complex.normSq (f.sum fun _ a => a) ≤ (s.card : ℝ) * (correlation f f 0).re := by
  have hsum : f.sum (fun _ a => a) = ∑ x ∈ s, f x :=
    Finset.sum_subset hf fun x _ hx => Finsupp.notMem_support_iff.mp hx
  have henergy : (correlation f f 0).re = ∑ x ∈ s, Complex.normSq (f x) := by
    rw [re_correlation_self_zero]
    apply Finset.sum_subset hf
    intro x _ hx
    change Complex.normSq (f x) = 0
    rw [Finsupp.notMem_support_iff.mp hx, Complex.normSq_zero]
  rw [hsum, henergy]
  exact normSq_sum_le_card_mul s f

/-- Differencing with a real, nonnegative correlation sum. -/
theorem vanDerCorput (N H : ℕ) (hH : 0 < H) (f : ℤ →₀ ℂ)
    (hf : f.support ⊆ interval N) :
    Complex.normSq (f.sum fun _ a => a) ≤ ((N : ℝ) + H) *
      (fejerWeight H).sum (fun h w => w * (correlation f f h).re) := by
  have hcard : (Finset.Icc (1 - (H : ℤ)) (N : ℤ)).card = N + H := by
    rw [Int.card_Icc]
    omega
  have h := finsupp_normSq_sum_le_card_mul (Finset.Icc (1 - (H : ℤ)) N)
    (movingAverage H f) (support_movingAverage_subset N H f hf)
  simpa only [sum_movingAverage H hH f, re_correlation_movingAverage, hcard,
    Nat.cast_add] using h

theorem vanDerCorput_norm (N H : ℕ) (hH : 0 < H) (f : ℤ →₀ ℂ)
    (hf : f.support ⊆ interval N) :
    ‖f.sum (fun _ a => a)‖ ^ 2 ≤ ((N : ℝ) + H) *
      (fejerWeight H).sum (fun h w => w * (correlation f f h).re) := by
  simpa only [Complex.normSq_eq_norm_sq] using vanDerCorput N H hH f hf

/-- Character twisting turns differencing into a Fourier bound. -/
theorem fourierSum_sq_le (N H : ℕ) (hH : 0 < H) (f : ℤ →₀ ℂ)
    (hf : f.support ⊆ interval N) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum f α‖ ^ 2 ≤ ((N : ℝ) + H) *
      (fejerWeight H).sum (fun h w => w * ‖correlation f f h‖) := by
  have htwist : (fourierTwist α f).support ⊆ interval N := by
    simpa only [support_fourierTwist] using hf
  have hvdc := vanDerCorput_norm N H hH (fourierTwist α f) htwist
  rw [sum_fourierTwist] at hvdc
  apply hvdc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (fejerWeight_nonneg H h)
  calc
    (correlation (fourierTwist α f) (fourierTwist α f) h).re ≤
        ‖correlation (fourierTwist α f) (fourierTwist α f) h‖ := Complex.re_le_norm _
    _ = ‖correlation f f h‖ := norm_correlation_fourierTwist α f f h

end Sidon
