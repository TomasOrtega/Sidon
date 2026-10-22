import Sidon.NumberTheory.LogSmoothing

/-! Absolute convergence justifications for smoothing a complex series. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Sidon

theorem intervalIntegral_tsum_of_uniform_norm_bound {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℂ) (m : ι → ℝ) (hf : ∀ i, Continuous (f i))
    (hm : Summable m) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ i u, u ∈ Set.Icc 0 T → ‖f i u‖ ≤ m i) :
    (∫ u in (0 : ℝ)..T, ∑' i, f i u) = ∑' i, ∫ u in (0 : ℝ)..T, f i u := by
  have hint : ∀ i, Integrable (f i) (volume.restrict (Set.Ioc 0 T)) := fun i =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp ((hf i).intervalIntegrable 0 T)
  have hnorm : Summable (fun i => ∫ u in Set.Ioc 0 T, ‖f i u‖) := by
    apply (hm.mul_right T).of_nonneg_of_le
    · intro i
      exact integral_nonneg fun _ => norm_nonneg _
    · intro i
      rw [← intervalIntegral.integral_of_le hT]
      calc
        _ ≤ ∫ _u in (0 : ℝ)..T, m i := by
          apply intervalIntegral.integral_mono_on hT
            ((hf i).norm.intervalIntegrable 0 T) intervalIntegrable_const
          exact fun u hu => hbound i u hu
        _ = m i * T := by simp [intervalIntegral.integral_const, mul_comm]
  simpa only [intervalIntegral.integral_of_le hT] using
    (integral_tsum_of_summable_integral_norm hint hnorm).symm

theorem logarithmicPrimitive_norm_le_of_bound {f : ℝ → ℂ} {m T : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T)
    (hbound : ∀ u, u ∈ Set.Icc 0 T → ‖f u‖ ≤ m) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖logarithmicPrimitive f n t‖ ≤ m * T ^ n := by
  induction n generalizing t with
  | zero => simpa only [logarithmicPrimitive, pow_zero, mul_one] using hbound t ht
  | succ n ih =>
      change ‖∫ u in (0 : ℝ)..t, logarithmicPrimitive f n u‖ ≤ _
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := m * T ^ n)
        (f := logarithmicPrimitive f n) (fun u hu => by
          rw [Set.uIoc_of_le ht.1] at hu
          exact ih ⟨hu.1.le, hu.2.trans ht.2⟩)
      rw [sub_zero, abs_of_nonneg ht.1] at hb
      exact hb.trans (by simpa [pow_succ, mul_assoc] using
        mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hm (pow_nonneg hT n)))

theorem summable_logarithmicPrimitive_of_uniform_bound {ι : Type*}
    (f : ι → ℝ → ℂ) (m : ι → ℝ) (hm : Summable m) (hm0 : ∀ i, 0 ≤ m i)
    {T : ℝ} (hT : 0 ≤ T) (hbound : ∀ i u, u ∈ Set.Icc 0 T → ‖f i u‖ ≤ m i)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Summable (fun i => logarithmicPrimitive (f i) n t) := by
  apply (hm.mul_right (T ^ n)).of_norm_bounded
  intro i
  exact logarithmicPrimitive_norm_le_of_bound (hm0 i) hT (hbound i) n ht

theorem logarithmicPrimitive_tsum_of_uniform_bound {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℂ) (m : ι → ℝ) (hf : ∀ i, Continuous (f i))
    (hm : Summable m) (hm0 : ∀ i, 0 ≤ m i) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ i u, u ∈ Set.Icc 0 T → ‖f i u‖ ≤ m i)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    logarithmicPrimitive (fun u => ∑' i, f i u) n t =
      ∑' i, logarithmicPrimitive (f i) n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      change (∫ u in (0 : ℝ)..t, logarithmicPrimitive (fun v => ∑' i, f i v) n u) = _
      calc
        _ = ∫ u in (0 : ℝ)..t, ∑' i, logarithmicPrimitive (f i) n u := by
          apply intervalIntegral.integral_congr_Ioo_of_le ht.1
          intro u hu
          exact ih ⟨hu.1.le, hu.2.le.trans ht.2⟩
        _ = _ := intervalIntegral_tsum_of_uniform_norm_bound
          (fun i => logarithmicPrimitive (f i) n) (fun i => m i * T ^ n)
          (fun i => continuous_logarithmicPrimitive (hf i) n)
          (hm.mul_right (T ^ n)) ht.1
          (fun i u hu => logarithmicPrimitive_norm_le_of_bound (hm0 i) hT
            (hbound i) n ⟨hu.1, hu.2.trans ht.2⟩)


theorem fwdDiff_iter_tsum_of_summable_shift {ι : Type*} (f : ι → ℝ → ℂ)
    (n : ℕ) (h t : ℝ)
    (hsum : ∀ k ≤ n, Summable (fun i => f i (t + (k : ℝ) * h))) :
    (fwdDiff h)^[n] (fun u => ∑' i, f i u) t = ∑' i, (fwdDiff h)^[n] (f i) t := by
  simp only [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul, nsmul_eq_mul]
  symm
  rw [Summable.tsum_finsetSum (fun k hk =>
    (hsum k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).mul_left _)]
  simp only [tsum_mul_left]

theorem spectralSmoothing_tsum_of_uniform_bound {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℂ) (m : ι → ℝ) (hf : ∀ i, Continuous (f i))
    (hm : Summable m) (hm0 : ∀ i, 0 ≤ m i) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ i u, u ∈ Set.Icc 0 T → ‖f i u‖ ≤ m i)
    (n : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hwindow : t + ((n + 2 : ℕ) : ℝ) * h ≤ T) :
    spectralSmoothing n h (fun u => ∑' i, f i u) t =
      ∑' i, spectralSmoothing n h (f i) t := by
  have harg : ∀ k ≤ n + 2, t + (k : ℝ) * h ∈ Set.Icc 0 T := by
    intro k hk
    refine ⟨add_nonneg ht (mul_nonneg (Nat.cast_nonneg _) hh), ?_⟩
    exact (add_le_add (le_refl t) (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hk : (k : ℝ) ≤ ((n + 2 : ℕ) : ℝ)) hh)).trans hwindow
  unfold spectralSmoothing
  calc
    _ = (fwdDiff h)^[n + 2] (fun u => ∑' i, logarithmicPrimitive (f i) n u) t := by
      simp only [fwdDiff_iter_eq_sum_shift]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      apply logarithmicPrimitive_tsum_of_uniform_bound f m hf hm hm0 hT hbound
      simpa only [nsmul_eq_mul] using harg k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := fwdDiff_iter_tsum_of_summable_shift (fun i => logarithmicPrimitive (f i) n)
      (n + 2) h t (fun k hk =>
        summable_logarithmicPrimitive_of_uniform_bound f m hm hm0 hT hbound n (harg k hk))

end Sidon
