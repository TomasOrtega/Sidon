import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # Finite mean squares of Dirichlet polynomials -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

/-- The additive character at an arbitrary real frequency, without a `2π` factor. -/
def frequencyChar (ω t : ℝ) : ℂ := Complex.exp ((ω : ℂ) * t * Complex.I)

@[simp] theorem frequencyChar_zero (t : ℝ) : frequencyChar 0 t = 1 := by
  simp [frequencyChar]

@[simp] theorem norm_frequencyChar (ω t : ℝ) : ‖frequencyChar ω t‖ = 1 := by
  simp [frequencyChar, Complex.norm_exp]

@[fun_prop] theorem continuous_frequencyChar (ω : ℝ) : Continuous (frequencyChar ω) := by
  unfold frequencyChar
  fun_prop

theorem frequencyChar_mul_conj (u v t : ℝ) :
    frequencyChar u t * conj (frequencyChar v t) = frequencyChar (u - v) t := by
  unfold frequencyChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

/-- The elementary off-diagonal integration bound, uniform in the endpoint. -/
theorem norm_integral_frequencyChar_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, frequencyChar ω t‖ ≤ 2 / |ω| := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have heq : (fun t : ℝ => frequencyChar ω t) =
      (fun t : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * t)) := by
    funext t
    unfold frequencyChar
    congr 1
    ring
  rw [heq, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  calc
    _ ≤ ‖Complex.exp (((ω : ℂ) * Complex.I) * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]

/-- A finite Dirichlet polynomial is obtained by setting `ω n = -log n`. -/
def finiteFrequencySum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ)
    (t : ℝ) : ℂ := ∑ i ∈ s, a i * frequencyChar (ω i) t

theorem continuous_finiteFrequencySum {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) : Continuous (finiteFrequencySum s a ω) := by
  unfold finiteFrequencySum
  fun_prop

theorem finiteFrequencySum_norm_sq {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    (‖finiteFrequencySum s a ω t‖ ^ 2 : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [finiteFrequencySum, map_sum, map_mul, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← frequencyChar_mul_conj]
  ring

/-- Exact finite mean-square expansion before the off-diagonal terms are bounded. -/
theorem integral_finiteFrequencySum_norm_sq {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖finiteFrequencySum s a ω t‖ ^ 2) =
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) *
        ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t).re := by
  have hpoint (t : ℝ) : ‖finiteFrequencySum s a ω t‖ ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
      congrArg Complex.re (finiteFrequencySum_norm_sq s a ω t)
  simp_rw [hpoint]
  rw [show (∫ t in (0 : ℝ)..T,
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re) =
      (∫ t in (0 : ℝ)..T,
        ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re from
    Complex.reCLM.intervalIntegral_comp_comm
      ((by fun_prop : Continuous (fun t : ℝ =>
        ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  congr 1
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (by fun_prop : Continuous (fun t : ℝ =>
      ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by fun_prop : Continuous (fun t : ℝ =>
      (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- Diagonal integration is exact; every distinct frequency costs its reciprocal gap. -/
theorem integral_finiteFrequencySum_norm_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ) (hω : Set.InjOn ω (s : Set ι)) :
    (∫ t in (0 : ℝ)..T, ‖finiteFrequencySum s a ω t‖ ^ 2) ≤
      T * ∑ i ∈ s, ‖a i‖ ^ 2 +
        ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else
          2 * ‖a i‖ * ‖a j‖ / |ω i - ω j| := by
  classical
  rw [integral_finiteFrequencySum_norm_sq]
  simp only [Complex.re_sum]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ((a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t).re ≤
        (if i = j then T * ‖a i‖ ^ 2 else 0) +
        (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, frequencyChar_zero, intervalIntegral.integral_const,
        sub_zero, Complex.real_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        ite_true, add_zero]
      simp [← Complex.ofReal_pow, mul_comm]
    · simp only [hij, ite_false, zero_add]
      have hgap : ω i - ω j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hω hi hj h))
      calc
        _ ≤ ‖(a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ :=
          Complex.re_le_norm _
        _ = (‖a i‖ * ‖a j‖) * ‖∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
        _ ≤ (‖a i‖ * ‖a j‖) * (2 / |ω i - ω j|) :=
          mul_le_mul_of_nonneg_left (norm_integral_frequencyChar_le hgap T) (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((if i = j then T * ‖a i‖ ^ 2 else 0) +
         (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      exact hpair i hi
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

end Sidon
