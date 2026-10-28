module

public import Sidon.NumberTheory.BSplinePrimitive

@[expose] public section

/-! Finite weighted detectors and their support localization. -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem fwdDiff_iter_sum_heavisidePrimitive {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ) (r : ℕ) (h t : ℝ) :
    (fwdDiff h)^[r] (fun u => ∑ n ∈ S, a n * heavisidePrimitive (r - 1) (u - b n)) t =
      ∑ n ∈ S, a n * primeDetectorKernel r h (t - b n) := by
  have hfun : (fun u => ∑ n ∈ S, a n * heavisidePrimitive (r - 1) (u - b n)) =
      ∑ n ∈ S, a n • (fun u => heavisidePrimitive (r - 1) (u - b n)) := by
    ext u
    simp
  rw [hfun, fwdDiff_iter_finsetSum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [fwdDiff_iter_const_smul]
  change a n * (fwdDiff h)^[r]
    (fun u => heavisidePrimitive (r - 1) (u + -b n)) t = _
  rw [fwdDiff_iter_comp_add]
  rfl

theorem sum_primeDetectorKernel_nonneg {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ) {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 ≤ h)
    (ha : ∀ n ∈ S, 0 ≤ a n) (t : ℝ) :
    0 ≤ ∑ n ∈ S, a n * primeDetectorKernel r h (t - b n) := by
  exact Finset.sum_nonneg fun n hn =>
    mul_nonneg (ha n hn) (primeDetectorKernel_bounds hr hh (t - b n)).1

theorem sum_primeDetectorKernel_le {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ) {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 ≤ h)
    (ha : ∀ n ∈ S, 0 ≤ a n) (t : ℝ) :
    (∑ n ∈ S, a n * primeDetectorKernel r h (t - b n)) ≤
      h ^ (r - 1) * ∑ n ∈ S, a n := by
  calc
    _ ≤ ∑ n ∈ S, a n * h ^ (r - 1) := Finset.sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_left (primeDetectorKernel_bounds hr hh (t - b n)).2 (ha n hn)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem exists_supported_weight_of_sum_primeDetectorKernel_pos {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ) {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 ≤ h)
    (ha : ∀ n ∈ S, 0 ≤ a n) (t : ℝ)
    (hpos : 0 < ∑ n ∈ S, a n * primeDetectorKernel r h (t - b n)) :
    ∃ n ∈ S, 0 < a n ∧ t ≤ b n ∧ b n ≤ t + (r : ℝ) * h := by
  obtain ⟨n, hn, hnpos⟩ := (Finset.sum_pos_iff_of_nonneg fun n hn =>
    mul_nonneg (ha n hn) (primeDetectorKernel_bounds hr hh (t - b n)).1).mp hpos
  have hapos : 0 < a n := pos_of_mul_pos_left hnpos
    (primeDetectorKernel_bounds hr hh (t - b n)).1
  have hkpos : 0 < primeDetectorKernel r h (t - b n) :=
    pos_of_mul_pos_right hnpos (ha n hn)
  have hsupp : t - b n ∈ Set.Icc (-(r : ℝ) * h) 0 :=
    support_primeDetectorKernel_subset hr hh (ne_of_gt hkpos)
  exact ⟨n, hn, hapos, by linarith [hsupp.2], by linarith [hsupp.1]⟩

end Sidon
