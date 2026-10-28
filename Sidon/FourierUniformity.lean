module

public import Sidon.Analysis.SidonCorrelation
public import Sidon.Analysis.UniformityEstimates

@[expose] public section

/-! # Fourier uniformity of extremal Sidon sets -/

noncomputable section

namespace Sidon

/-- The balanced difference between a set and its constant-density interval model. -/
def discrepancyFunction (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  indicatorFinsupp S - intervalModel N S

/-- The relative deviation of the cardinality from the extremal scale. -/
def sidonDeviation (N : ℕ) (S : Finset ℤ) : ℝ :=
  |(S.card : ℝ) / Real.sqrt N - 1|

theorem support_discrepancyFunction {N : ℕ} {S : Finset ℤ} (hSN : S ⊆ interval N) :
    (discrepancyFunction N S).support ⊆ interval N := by
  intro x hx
  by_contra hxn
  have hxs : x ∉ S := fun hs => hxn (hSN hs)
  apply Finsupp.mem_support_iff.mp hx
  simp [discrepancyFunction, intervalModel, indicatorFinsupp_apply, hxs, hxn]

private theorem indicatorFinsupp_im (S : Finset ℤ) (x : ℤ) :
    (indicatorFinsupp S x).im = 0 := by
  by_cases hx : x ∈ S <;> simp [indicatorFinsupp_apply, hx]

private theorem discrepancyFunction_im (N : ℕ) (S : Finset ℤ) (x : ℤ) :
    (discrepancyFunction N S x).im = 0 := by
  simp only [discrepancyFunction, Finsupp.sub_apply, Complex.sub_im,
    indicatorFinsupp_im, intervalModel, Finsupp.smul_apply, Complex.smul_im,
    mul_zero, smul_zero, sub_zero]

private theorem correlation_im_of_real (f g : ℤ →₀ ℂ)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) (h : ℤ) :
    (correlation f g h).im = 0 := by
  simp [correlation, Finsupp.sum, Complex.mul_im, hf, hg]

theorem norm_correlation_discrepancy_le (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    ‖correlation (discrepancyFunction N S) (discrepancyFunction N S) h‖ ≤
      |(S.card : ℝ) ^ 2 / N - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| +
      |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (intervalModel N S) h).re| +
      |(S.card : ℝ) ^ 2 / N - (correlation (indicatorFinsupp S) (intervalModel N S) h).re| +
      |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (indicatorFinsupp S) h).re| := by
  let a := indicatorFinsupp S
  let b := intervalModel N S
  let t : ℝ := (S.card : ℝ) ^ 2 / N
  have him := correlation_im_of_real (discrepancyFunction N S) (discrepancyFunction N S)
    (discrepancyFunction_im N S) (discrepancyFunction_im N S) h
  have heq : correlation (discrepancyFunction N S) (discrepancyFunction N S) h =
      (((correlation a a h).re - (correlation a b h).re -
        (correlation b a h).re + (correlation b b h).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [discrepancyFunction, correlation_sub_left, correlation_sub_right,
        Complex.sub_re, Complex.ofReal_re]
      dsimp only [a, b]
      ring
    · simpa only [Complex.ofReal_im] using him
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  change |(correlation a a h).re - (correlation a b h).re -
    (correlation b a h).re + (correlation b b h).re| ≤ _
  apply abs_le.mpr
  constructor <;> dsimp only [a, b] at * <;>
    linarith [le_abs_self (t - (correlation a a h).re),
      neg_le_abs (t - (correlation a a h).re),
      le_abs_self (t - (correlation a b h).re), neg_le_abs (t - (correlation a b h).re),
      le_abs_self (t - (correlation b a h).re), neg_le_abs (t - (correlation b a h).re),
      le_abs_self (t - (correlation b b h).re), neg_le_abs (t - (correlation b b h).re)]

theorem discrepancy_fourier_sq_le_errors {N H : ℕ} (hH : 0 < H)
    {S : Finset ℤ} (hSN : S ⊆ interval N) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤ ((N : ℝ) + H) *
      (correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) +
        correlationError N S H (intervalModel N S) (intervalModel N S) +
        correlationError N S H (indicatorFinsupp S) (intervalModel N S) +
        correlationError N S H (intervalModel N S) (indicatorFinsupp S)) := by
  apply (fourierSum_sq_le N H hH (discrepancyFunction N S)
    (support_discrepancyFunction hSN) α).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (fejerWeight H).sum (fun h w => w *
        ‖correlation (discrepancyFunction N S) (discrepancyFunction N S) h‖) ≤
        (fejerWeight H).sum (fun h w => w *
          (|(S.card : ℝ) ^ 2 / N - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| +
          |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (intervalModel N S) h).re| +
          |(S.card : ℝ) ^ 2 / N - (correlation (indicatorFinsupp S) (intervalModel N S) h).re| +
          |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (indicatorFinsupp S) h).re|)) := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left (norm_correlation_discrepancy_le N S h)
        (fejerWeight_nonneg H h)
    _ = _ := by simp only [correlationError, Finsupp.sum, mul_add, Finset.sum_add_distrib]

theorem sidon_fourier_discrepancy_sq_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hHN : H ≤ N) {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ))
    (hSN : S ⊆ interval N) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (discrepancyFunction N S) α‖ ^ 2 ≤
      24 * N * sidonDeviation N S + 20 * N * Real.sqrt N / H +
        200 * Real.sqrt N * Real.sqrt H := by
  have hmix : correlationError N S H (indicatorFinsupp S) (intervalModel N S) ≤
      5 * (S.card : ℝ) * Real.sqrt H / N := by
    apply (mixed_correlationError_le hH hS hSN).trans
    have hz : 0 ≤ (S.card : ℝ) * Real.sqrt H / N := by positivity
    ring_nf at hz ⊢
    linarith
  have hmix' : correlationError N S H (intervalModel N S) (indicatorFinsupp S) ≤
      5 * (S.card : ℝ) * Real.sqrt H / N := by
    rw [correlationError_swap]
    exact hmix
  apply (discrepancy_fourier_sq_le_errors hH hSN α).trans
  exact fourier_error_master_le (by positivity) (by positivity)
    (by exact_mod_cast hHN) (Nat.cast_nonneg _) (hS.card_le_five_mul_sqrt hSN)
    (self_correlationError_le hN hH hS hSN)
    (intervalModel_correlationError_le hN hH hHN S) hmix hmix'

/-- Theorem 1.2, pointwise, with an absolute constant of sixteen. -/
theorem sidon_fourier_uniformity_apply {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum (discrepancyFunction N S) α‖ ≤
      16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  apply fourier_uniformity_of_window_estimates hN (abs_nonneg _) (norm_nonneg _)
  intro H hH hHN
  exact sidon_fourier_discrepancy_sq_le hN hH hHN hS hSN α

theorem fourierSum_discrepancyFunction (N : ℕ) (S : Finset ℤ) :
    fourierSum (discrepancyFunction N S) = fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N)) := by
  simp only [discrepancyFunction, intervalModel, fourierSum_sub, fourierSum_real_smul]

/-- Fourier uniformity in supremum norm, as in Theorem 1.2 of the paper. -/
theorem sidon_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    ‖fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
      16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  rw [← fourierSum_discrepancyFunction]
  exact (ContinuousMap.norm_le (fourierSum (discrepancyFunction N S)) (by positivity)).mpr
    (sidon_fourier_uniformity_apply hN hS hSN)

end Sidon
