/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.SumIntegralComparisons
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianKernel
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianResonance
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovGaussianSpacing
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
theorem integerDistance_eq_abs {x : ℝ} (hx : |x| ≤ 1 / 2) :
    integerDistance x = |x| := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  rcases le_or_gt x 0 with h | h
  · have hf : Int.fract (-x) = -x := Int.fract_eq_self.mpr ⟨neg_nonneg.mpr h, by linarith⟩
    rw [integerDistance, hf, abs_of_nonpos h, min_eq_left]
    linarith
  · have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨h.le, by linarith⟩
    have hf0 : Int.fract x ≠ 0 := by rw [hf]; exact ne_of_gt h
    rw [integerDistance, Int.fract_neg hf0, hf, sub_sub_cancel, abs_of_pos h, min_eq_right]
    linarith

theorem gaussian_antitone {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Set.Ici 0) := by
  intro x hx y _ hxy
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx hxy 2) (neg_nonpos.mpr hc.le)

theorem nat_gaussian_sum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * (n : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / c) / 2 := by
  have h := (gaussian_antitone hc).tsum_le_integral
    (integrable_exp_neg_mul_sq hc).integrableOn
    (fun _ _ => (Real.exp_pos _).le)
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero,
    integral_gaussian_Ioi] using h

theorem summable_gaussian_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  simpa only [zero_mul, add_zero] using summable_real_quadratic (neg_lt_zero.mpr hc) 0 0

theorem int_gaussian_sum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / c) := by
  have hnat := (gaussian_antitone hc).summable_of_integrableOn_Ioi_zero
    (integrable_exp_neg_mul_sq hc).integrableOn (fun _ _ => (Real.exp_pos _).le)
  have hpos := hnat.comp_injective (show Function.Injective (fun n : ℕ => n + 1) from
    fun _ _ h => Nat.add_right_cancel h)
  have hneg : Summable (fun n : ℕ => Real.exp (-c * ((-(n + 1) : ℤ) : ℝ) ^ 2)) := by
    simpa only [Function.comp_def, Int.cast_neg, Int.cast_add, Int.cast_natCast,
      Int.cast_one, neg_sq, Nat.cast_add, Nat.cast_one] using hpos
  have htail := (gaussian_antitone hc).tsum_add_one_le_integral
    (integrable_exp_neg_mul_sq hc).integrableOn (fun _ _ => (Real.exp_pos _).le)
  rw [integral_gaussian_Ioi] at htail
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) hnat hneg]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq]
  have hbase := nat_gaussian_sum_le hc
  simp only [Nat.cast_add, Nat.cast_one] at htail
  linarith only [hbase, htail]

theorem finite_envelope_le {a gamma : ℝ} (ha : 0 < a) (hg : gamma ≠ 0)
    (S : Finset ℤ) (hphase : ∀ n ∈ S, |gamma * (n : ℝ)| ≤ 1 / 2) :
    ∑ n ∈ S, tailEnvelope a (gamma * (n : ℝ)) ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        (1 + Real.sqrt (Real.pi / (Real.pi * gamma ^ 2 / a))) := by
  let c := Real.pi * gamma ^ 2 / a
  have hc : 0 < c := div_pos (mul_pos Real.pi_pos (sq_pos_of_ne_zero hg)) ha
  have he (n : ℤ) (hn : n ∈ S) :
      tailEnvelope a (gamma * (n : ℝ)) ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        Real.exp (-c * (n : ℝ) ^ 2) := by
    have h := tailEnvelope_le_distance ha (gamma * (n : ℝ))
    rw [integerDistance_eq_abs (hphase n hn), sq_abs] at h
    convert h using 1
    dsimp only [c]
    congr 2
    ring
  have hp : 0 ≤ 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a))) :=
    div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _) (tail_denominator_pos ha).le)
  calc
    _ ≤ ∑ n ∈ S, (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        Real.exp (-c * (n : ℝ) ^ 2) := Finset.sum_le_sum he
    _ = _ * ∑ n ∈ S, Real.exp (-c * (n : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ * (∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left ((summable_gaussian_int hc).sum_le_tsum S
        (fun _ _ => (Real.exp_pos _).le)) hp
    _ ≤ _ := mul_le_mul_of_nonneg_left (int_gaussian_sum_le hc) hp

theorem finite_envelope_le_width {a gamma : ℝ} (ha : 0 < a) (hg : gamma ≠ 0)
    (S : Finset ℤ) (hphase : ∀ n ∈ S, |gamma * (n : ℝ)| ≤ 1 / 2) :
    ∑ n ∈ S, tailEnvelope a (gamma * (n : ℝ)) ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        (1 + Real.sqrt a / |gamma|) := by
  have h := finite_envelope_le ha hg S hphase
  have he : Real.pi / (Real.pi * gamma ^ 2 / a) = a / gamma ^ 2 := by
    field_simp
  rw [he, Real.sqrt_div ha.le, Real.sqrt_sq_eq_abs] at h
  exact h

theorem tailEnvelope_le_prefactor {a : ℝ} (ha : 0 < a) (x : ℝ) :
    tailEnvelope a x ≤ 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a))) := by
  have hp : 0 ≤ 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a))) :=
    div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _) (tail_denominator_pos ha).le)
  apply (tailEnvelope_le_distance ha x).trans
  have he : Real.exp (-Real.pi * integerDistance x ^ 2 / a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (sq_nonneg _)) ha.le)
  simpa using mul_le_mul_of_nonneg_left he hp

theorem resonanceEnvelope_le_coordinate_sums {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (gamma : Fin k → ℝ)
    (v : ι → Fin k → ℤ) (S : Fin k → Finset ℤ)
    (hsupport : ∀ h ∈ VinogradovGaussianResonance.differenceSupport
      (VinogradovShiftedMoment.tupleFrequency s v), ∀ j, h j ∈ S j) :
    resonanceEnvelope s a gamma v ≤
      ∏ j, ∑ n ∈ S j, tailEnvelope (a j) (gamma j * (n : ℝ)) := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    exact Fintype.mem_piFinset.mpr (hsupport h hh)
  · intro h _ _
    exact Finset.prod_nonneg (fun j _ => (tailEnvelope_pos (ha j) _).le)

theorem resonanceEnvelope_le_selected_widths {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (gamma : Fin k → ℝ)
    (v : ι → Fin k → ℤ) (S : Fin k → Finset ℤ) (R : Finset (Fin k))
    (hsupport : ∀ h ∈ VinogradovGaussianResonance.differenceSupport
      (VinogradovShiftedMoment.tupleFrequency s v), ∀ j, h j ∈ S j)
    (hgamma : ∀ j ∈ R, gamma j ≠ 0)
    (hphase : ∀ j ∈ R, ∀ n ∈ S j, |gamma j * (n : ℝ)| ≤ 1 / 2) :
    resonanceEnvelope s a gamma v ≤
      ∏ j, (2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j)))) *
        if j ∈ R then min ((S j).card : ℝ) (1 + Real.sqrt (a j) / |gamma j|)
          else ((S j).card : ℝ) := by
  classical
  apply (resonanceEnvelope_le_coordinate_sums s ha gamma v S hsupport).trans
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.sum_nonneg (fun _ _ => (tailEnvelope_pos (ha j) _).le)
  · intro j _
    have hc : (∑ n ∈ S j, tailEnvelope (a j) (gamma j * (n : ℝ))) ≤
        (2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j)))) * (S j).card := by
      calc
        _ ≤ ∑ _n ∈ S j, 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
          Finset.sum_le_sum (fun _ _ => tailEnvelope_le_prefactor (ha j) _)
        _ = _ := by simp [mul_comm]
    split_ifs with hj
    · have hp : 0 ≤ 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
        div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j).le _)
          (tail_denominator_pos (ha j)).le)
      rw [mul_min_of_nonneg _ _ hp]
      exact le_min hc (finite_envelope_le_width (ha j) (hgamma j hj) (S j) (hphase j hj))
    · exact hc

end
end RiemannGaussian.VinogradovGaussianSpacing
