import Sidon.NumberTheory.BSplineDetector
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! Higher logarithmic primitives of the actual finite von Mangoldt sum. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

def smoothedMangoldtTerm (j n : ℕ) (t : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * heavisidePrimitive (j + 1) (t - Real.log n)

def smoothedMangoldt (j : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, smoothedMangoldtTerm j n t

theorem smoothedMangoldtTerm_eq_zero_of_not_mem (j : ℕ) {n : ℕ} {t : ℝ}
    (hn : n ∉ Finset.Icc 1 ⌊Real.exp t⌋₊) : smoothedMangoldtTerm j n t = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothedMangoldtTerm]
  have hnl : ⌊Real.exp t⌋₊ < n := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have ht : t < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).mpr ((Nat.floor_lt (Real.exp_pos t).le).mp hnl)
  rw [smoothedMangoldtTerm, heavisidePrimitive_succ_eq_zero_of_nonpos j (by linarith), mul_zero]

theorem smoothedMangoldt_eq_fixed_sum (j : ℕ) {t T : ℝ} (ht : t ≤ T) :
    smoothedMangoldt j t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, smoothedMangoldtTerm j n t := by
  unfold smoothedMangoldt
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono (Real.exp_le_exp.mpr ht))⟩
  · intro n _ hn
    exact smoothedMangoldtTerm_eq_zero_of_not_mem j hn

theorem continuous_smoothedMangoldtTerm (j n : ℕ) : Continuous (smoothedMangoldtTerm j n) := by
  exact continuous_const.mul ((continuous_heavisidePrimitive_succ j).comp
    (continuous_id.sub continuous_const))

theorem continuous_smoothedMangoldt (j : ℕ) : Continuous (smoothedMangoldt j) := by
  rw [continuous_iff_continuousAt]
  intro t
  have he : smoothedMangoldt j =ᶠ[nhds t]
      (fun u => ∑ n ∈ Finset.Icc 1 ⌊Real.exp (t + 1)⌋₊, smoothedMangoldtTerm j n u) := by
    filter_upwards [Iio_mem_nhds (show t < t + 1 by linarith)] with u hu
    exact smoothedMangoldt_eq_fixed_sum j hu.le
  apply (continuousAt_congr he).mpr
  exact (continuous_finsetSum _ (fun n _ => continuous_smoothedMangoldtTerm j n)).continuousAt


theorem integral_smoothedMangoldtTerm (j n : ℕ) (t : ℝ) :
    (∫ v in (0 : ℝ)..t, smoothedMangoldtTerm j n v) = smoothedMangoldtTerm (j + 1) n t := by
  unfold smoothedMangoldtTerm
  rw [intervalIntegral.integral_const_mul]
  change ArithmeticFunction.vonMangoldt n *
    (∫ v in (0 : ℝ)..t, heavisidePrimitive (j + 1) (v + -Real.log n)) = _
  rw [integral_heavisidePrimitive_translate]
  have hz : heavisidePrimitive (j + 1 + 1) (-Real.log n) = 0 :=
    heavisidePrimitive_succ_eq_zero_of_nonpos (j + 1)
      (neg_nonpos.mpr (Real.log_natCast_nonneg n))
  simp [hz, sub_eq_add_neg]

theorem integral_smoothedMangoldt (j : ℕ) (t : ℝ) :
    (∫ v in (0 : ℝ)..t, smoothedMangoldt j v) = smoothedMangoldt (j + 1) t := by
  let T := max t 0
  calc
    _ = ∫ v in (0 : ℝ)..t,
        ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, smoothedMangoldtTerm j n v := by
      apply intervalIntegral.integral_congr
      intro v hv
      apply smoothedMangoldt_eq_fixed_sum
      simpa only [T, max_comm] using hv.2
    _ = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        ∫ v in (0 : ℝ)..t, smoothedMangoldtTerm j n v := by
      rw [intervalIntegral.integral_finsetSum]
      intro n _
      exact (continuous_smoothedMangoldtTerm j n).intervalIntegrable 0 t
    _ = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, smoothedMangoldtTerm (j + 1) n t := by
      apply Finset.sum_congr rfl
      intro n _
      exact integral_smoothedMangoldtTerm j n t
    _ = _ := (smoothedMangoldt_eq_fixed_sum (j + 1) (le_max_left t 0)).symm


theorem fwdDiff_iter_smoothedMangoldt (j : ℕ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    (fwdDiff h)^[j + 2] (smoothedMangoldt j) t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (t + ((j + 2 : ℕ) : ℝ) * h)⌋₊,
        ArithmeticFunction.vonMangoldt n * primeDetectorKernel (j + 2) h (t - Real.log n) := by
  let T := t + ((j + 2 : ℕ) : ℝ) * h
  calc
    _ = (fwdDiff h)^[j + 2]
        (fun u => ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, smoothedMangoldtTerm j n u) t := by
      simp only [fwdDiff_iter_eq_sum_shift]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      apply smoothedMangoldt_eq_fixed_sum
      have hk' : (k : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      simpa only [T, nsmul_eq_mul] using add_le_add (le_refl t) (mul_le_mul_of_nonneg_right hk' hh)
    _ = _ := by
      simpa only [T, smoothedMangoldtTerm, show j + 2 - 1 = j + 1 by omega] using
        fwdDiff_iter_sum_heavisidePrimitive (Finset.Icc 1 ⌊Real.exp T⌋₊)
          (fun n => ArithmeticFunction.vonMangoldt n) (fun n => Real.log n) (j + 2) h t

end Sidon
