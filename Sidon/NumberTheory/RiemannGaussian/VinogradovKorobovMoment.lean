/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Data.List.Permutation
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianCentering
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianKernel
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianResonance
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentReduction
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovKorobovMoment
noncomputable section
open UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovMomentReduction
open RiemannGaussian.VinogradovKorobovBilinearPhase
open scoped BigOperators

def coordinates (k : ℕ) (t z b : ℝ) (j : Fin k) : ℝ :=
  (-t * (-1 : ℝ) ^ j.val / ((j.val + 1) * z ^ (j.val + 1))) *
    b ^ (j.val + 1) / (2 * Real.pi)

def sample (k : ℕ) (t z b : ℝ) : UnitAddTorus (Fin k) :=
  fun j => (coordinates k t z b j : UnitAddCircle)

theorem polynomial_eq_pairing (k : ℕ) (t z : ℝ) (a b : ℕ) :
    polynomial k t z a b =
      (2 * Real.pi) * ∑ j : Fin k, (monomialFrequency k a j : ℝ) * coordinates k t z b j := by
  rw [polynomial, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [monomialFrequency, coordinates, Int.cast_pow, Int.cast_natCast]
  let c := -t * (-1 : ℝ) ^ j.val / ((j.val + 1) * z ^ (j.val + 1))
  change c * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1) =
    (2 * Real.pi) * ((a : ℝ) ^ (j.val + 1) * (c * (b : ℝ) ^ (j.val + 1) / (2 * Real.pi)))
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  symm
  calc
    _ = (a : ℝ) ^ (j.val + 1) *
        ((c * (b : ℝ) ^ (j.val + 1) / (2 * Real.pi)) * (2 * Real.pi)) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hπ]; ring

theorem mFourier_eq_polynomialPhase (k : ℕ) (t z : ℝ) (a b : ℕ) :
    mFourier (monomialFrequency k a) (sample k t z b) = polynomialPhase k t z a b := by
  change mFourier (monomialFrequency k a)
    (fun j => (coordinates k t z b j : UnitAddCircle)) = _
  rw [mFourier_real_phase, polynomialPhase, polynomial_eq_pairing]
  congr 1
  push_cast
  ring

theorem polynomial_bound (k : ℕ) (t z : ℝ) (A B : Finset ℕ)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ‖∑ a ∈ A, ∑ b ∈ B, polynomialPhase k t z a b‖ ^ (2 * r * s) ≤
      (B.card : ℝ) ^ ((r - 1) * (2 * s)) *
      (A.card : ℝ) ^ (r * (2 * s - 2)) *
      moment r (fun a : A => monomialFrequency k a.val) *
      dualMoment r s (fun a : A => monomialFrequency k a.val)
        (fun b : B => sample k t z b.val)
        (alignmentWeights r (fun a : A => monomialFrequency k a.val)
          (fun b : B => sample k t z b.val)) := by
  have h := two_holder_bound hr hs
    (fun a : A => monomialFrequency k a.val) (fun b : B => sample k t z b.val)
  have he : (∑ b : B, ∑ a : A, mFourier (monomialFrequency k a.val)
      (sample k t z b.val)) = ∑ a ∈ A, ∑ b ∈ B, polynomialPhase k t z a b := by
    simp_rw [mFourier_eq_polynomialPhase]
    calc
      _ = ∑ b : B, ∑ a ∈ A, polynomialPhase k t z a b.val := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_coe_sort A (fun a : ℕ => polynomialPhase k t z a b.val)
      _ = ∑ b ∈ B, ∑ a ∈ A, polynomialPhase k t z a b :=
        Finset.sum_coe_sort B (fun b : ℕ => ∑ a ∈ A, polynomialPhase k t z a b)
      _ = _ := Finset.sum_comm
  simpa only [he, Fintype.card_coe] using h

theorem interval_bound (k M : ℕ) (t z : ℝ) (B : Finset ℕ)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ‖∑ a : Fin M, ∑ b ∈ B, polynomialPhase k t z ((a.val + 1 : ℕ) : ℝ) b‖ ^ (2 * r * s) ≤
      (B.card : ℝ) ^ ((r - 1) * (2 * s)) * (M : ℝ) ^ (r * (2 * s - 2)) *
      meanValue r k M * dualMoment r s
        (fun a : Fin M => monomialFrequency k (a.val + 1))
        (fun b : B => sample k t z b.val)
        (alignmentWeights r (fun a : Fin M => monomialFrequency k (a.val + 1))
          (fun b : B => sample k t z b.val)) := by
  have h := two_holder_bound hr hs
    (fun a : Fin M => monomialFrequency k (a.val + 1)) (fun b : B => sample k t z b.val)
  simp only [mFourier_eq_polynomialPhase, Fintype.card_coe, Fintype.card_fin] at h
  rw [Finset.sum_comm] at h
  have he (a : Fin M) : (∑ b : B, polynomialPhase k t z ((a.val + 1 : ℕ) : ℝ) b.val) =
      ∑ b ∈ B, polynomialPhase k t z ((a.val + 1 : ℕ) : ℝ) b :=
    Finset.sum_coe_sort B (fun b : ℕ => polynomialPhase k t z ((a.val + 1 : ℕ) : ℝ) b)
  simpa only [he, meanValue] using h

def phaseCoefficients (k : ℕ) (t z : ℝ) (j : Fin k) : ℝ :=
  (-t * (-1 : ℝ) ^ j.val / ((j.val + 1) * z ^ (j.val + 1))) / (2 * Real.pi)

theorem coordinates_eq_linearSample (k : ℕ) (t z : ℝ) (b : ℕ) :
    coordinates k t z b = VinogradovGaussianResonance.linearSample
      (phaseCoefficients k t z) (monomialFrequency k b) := by
  ext j
  simp only [coordinates, VinogradovGaussianResonance.linearSample,
    phaseCoefficients, monomialFrequency, Int.cast_pow, Int.cast_natCast]
  ring

theorem interval_frequency_bounds (r k M : ℕ) {n : Fin k → ℤ}
    (hn : n ∈ frequencySupport (VinogradovShiftedMoment.tupleFrequency r
      (fun b : Fin M => monomialFrequency k (b.val + 1)))) :
    ∀ j, (r : ℤ) ≤ n j ∧ n j ≤ (r : ℤ) * (M : ℤ) ^ (j.val + 1) := by
  classical
  let : DecidableEq (Fin k → ℤ) := Classical.decEq _
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hn
  intro j
  simp only [VinogradovShiftedMoment.tupleFrequency, Finset.sum_apply,
    monomialFrequency, Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      (r : ℤ) = ∑ _i : Fin r, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => one_le_pow₀ (by omega))
  · calc
      _ ≤ ∑ _i : Fin r, (M : ℤ) ^ (j.val + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply pow_le_pow_left₀ (by positivity)
        have h := (f i).isLt
        omega
      _ = _ := by simp

def intervalCenter (r k M : ℕ) (j : Fin k) : ℤ :=
  VinogradovGaussianCentering.integerMidpoint r ((r : ℤ) * (M : ℤ) ^ (j.val + 1))

theorem interval_centered_cost_le (r k M : ℕ) {a : Fin k → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    VinogradovGaussianKernel.supportCost a
      (VinogradovGaussianCentering.centeredSupport
        (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
          (fun b : Fin M => monomialFrequency k (b.val + 1)))) (intervalCenter r k M)) ≤
      ∑ j, Real.pi * a j * (((r : ℝ) * (M : ℝ) ^ (j.val + 1) - r + 1) / 2) ^ 2 := by
  have h := VinogradovGaussianCentering.midpoint_cost_le ha
    (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
      (fun b : Fin M => monomialFrequency k (b.val + 1))))
    (fun _ => (r : ℤ)) (fun j : Fin k => (r : ℤ) * (M : ℤ) ^ (j.val + 1))
    (fun _ hn => interval_frequency_bounds r k M hn)
  change VinogradovGaussianKernel.supportCost a
    (VinogradovGaussianCentering.centeredSupport
      (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
        (fun b : Fin M => monomialFrequency k (b.val + 1)))) (intervalCenter r k M)) ≤ _ at h
  simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_pow] using h

theorem interval_origin_cost_eq (r k : ℕ) {M : ℕ} (hM : 0 < M)
    {a : Fin k → ℝ} (ha : ∀ j, 0 ≤ a j) :
    VinogradovGaussianKernel.supportCost a
      (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
        (fun b : Fin M => monomialFrequency k (b.val + 1)))) =
      ∑ j, Real.pi * a j * ((r : ℝ) * (M : ℝ) ^ (j.val + 1)) ^ 2 := by
  classical
  let : DecidableEq (Fin k → ℤ) := Classical.decEq _
  let C := frequencySupport (VinogradovShiftedMoment.tupleFrequency r
    (fun b : Fin M => monomialFrequency k (b.val + 1)))
  have htop : (fun j : Fin k => (r : ℤ) * (M : ℤ) ^ (j.val + 1)) ∈ C := by
    refine Finset.mem_image.mpr ⟨(fun _ : Fin r => (⟨M - 1, by omega⟩ : Fin M)),
      Finset.mem_univ _, ?_⟩
    ext j
    simp only [VinogradovShiftedMoment.tupleFrequency, Finset.sum_apply, monomialFrequency,
      Nat.sub_add_cancel hM, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_antisymm
  · have h := VinogradovGaussianCentering.centered_cost_le ha C 0
      (fun j : Fin k => (r : ℝ) * (M : ℝ) ^ (j.val + 1)) (by
        intro n hn j
        have hbounds := interval_frequency_bounds r k M hn j
        have hn₀ : (0 : ℤ) ≤ n j := (Nat.cast_nonneg r).trans hbounds.1
        have hn₀' : (0 : ℝ) ≤ n j := by exact_mod_cast hn₀
        have hn₁ : (n j : ℝ) ≤ (r : ℝ) * (M : ℝ) ^ (j.val + 1) := by
          exact_mod_cast hbounds.2
        simpa only [Pi.zero_apply, Int.cast_zero, sub_zero, abs_of_nonneg hn₀'] using hn₁)
    have hzero : VinogradovGaussianCentering.centeredSupport C 0 = C := by
      unfold VinogradovGaussianCentering.centeredSupport
      simp
    rw [hzero] at h
    exact h
  · have h := VinogradovGaussianKernel.frequencyCost_le_supportCost a C htop
    simpa only [VinogradovGaussianKernel.frequencyCost, Int.cast_mul,
      Int.cast_natCast, Int.cast_pow] using h

theorem interval_centered_cost_le_quarter {r M : ℕ} (hr : 1 ≤ r) (hM : 0 < M)
    (k : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 ≤ a j) :
    VinogradovGaussianKernel.supportCost a
      (VinogradovGaussianCentering.centeredSupport
        (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
          (fun b : Fin M => monomialFrequency k (b.val + 1)))) (intervalCenter r k M)) ≤
      VinogradovGaussianKernel.supportCost a
        (frequencySupport (VinogradovShiftedMoment.tupleFrequency r
          (fun b : Fin M => monomialFrequency k (b.val + 1)))) / 4 := by
  apply (interval_centered_cost_le r k M ha).trans
  rw [interval_origin_cost_eq r k hM ha, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (1 : ℝ) ≤ (M : ℝ) ^ (j.val + 1) := one_le_pow₀ hM'
  have hR₀ : 0 ≤ ((r : ℝ) * (M : ℝ) ^ (j.val + 1) - r + 1) / 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg r) (sub_nonneg.mpr hp)]
  have hR₁ : ((r : ℝ) * (M : ℝ) ^ (j.val + 1) - r + 1) / 2 ≤
      (r : ℝ) * (M : ℝ) ^ (j.val + 1) / 2 := by linarith
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR₀ hR₁ 2)
    (mul_nonneg Real.pi_pos.le (ha j))
  convert h using 1; ring

theorem interval_centered_envelope_bound (k M : ℕ) (t z : ℝ) (B : Finset ℕ)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) (m : Fin k → ℤ) :
    let v := fun b : Fin M => monomialFrequency k (b.val + 1)
    let u := fun b : B => monomialFrequency k b.val
    ‖∑ b : Fin M, ∑ c ∈ B,
        polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * s) ≤
      (B.card : ℝ) ^ ((r - 1) * (2 * s)) * (M : ℝ) ^ (r * (2 * s - 2)) *
        meanValue r k M *
        Real.exp (VinogradovGaussianKernel.supportCost a
          (VinogradovGaussianCentering.centeredSupport
            (frequencySupport (VinogradovShiftedMoment.tupleFrequency r v)) m)) *
        moment s u *
        VinogradovGaussianBounds.resonanceEnvelope s a (phaseCoefficients k t z) u := by
  dsimp only
  have hG := VinogradovGaussianCentering.dualMoment_le_centered_resonance r s
    (fun b : Fin M => monomialFrequency k (b.val + 1))
    (fun b : B => monomialFrequency k b.val) (phaseCoefficients k t z)
    (alignmentWeights r (fun b : Fin M => monomialFrequency k (b.val + 1))
      (fun b : B => sample k t z b.val))
    (norm_alignmentWeights r (fun b : Fin M => monomialFrequency k (b.val + 1))
      (fun b : B => sample k t z b.val)) m ha
  simp only [← coordinates_eq_linearSample] at hG
  have hR := VinogradovGaussianBounds.resonanceSum_le_envelope s ha
    (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val)
  have hJ : 0 ≤ meanValue r k M :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hK : 0 ≤ moment s (fun b : B => monomialFrequency k b.val) :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hG' := hG.trans (mul_le_mul_of_nonneg_left hR
    (mul_nonneg (Real.exp_pos _).le hK))
  change dualMoment r s (fun b : Fin M => monomialFrequency k (b.val + 1))
    (fun b : B => sample k t z b.val)
    (alignmentWeights r (fun b : Fin M => monomialFrequency k (b.val + 1))
      (fun b : B => sample k t z b.val)) ≤ _ at hG'
  have hp : 0 ≤ (B.card : ℝ) ^ ((r - 1) * (2 * s)) *
      (M : ℝ) ^ (r * (2 * s - 2)) * meanValue r k M := by positivity
  apply (interval_bound k M t z B hr hs).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hG' hp

theorem interval_quarter_envelope_bound (k : ℕ) {M : ℕ} (hM : 0 < M)
    (t z : ℝ) (B : Finset ℕ) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    let v := fun b : Fin M => monomialFrequency k (b.val + 1)
    let u := fun b : B => monomialFrequency k b.val
    ‖∑ b : Fin M, ∑ c ∈ B,
        polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * s) ≤
      (B.card : ℝ) ^ ((r - 1) * (2 * s)) * (M : ℝ) ^ (r * (2 * s - 2)) *
        meanValue r k M *
        Real.exp (VinogradovGaussianKernel.supportCost a
          (frequencySupport (VinogradovShiftedMoment.tupleFrequency r v)) / 4) *
        moment s u *
        VinogradovGaussianBounds.resonanceEnvelope s a (phaseCoefficients k t z) u := by
  dsimp only
  have hQ := Real.exp_le_exp.mpr
    (interval_centered_cost_le_quarter hr hM k (fun j => (ha j).le))
  have hJ : 0 ≤ meanValue r k M :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hK : 0 ≤ moment s (fun b : B => monomialFrequency k b.val) :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hE := VinogradovGaussianBounds.resonanceEnvelope_nonneg s ha
    (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val)
  have hp : 0 ≤ (B.card : ℝ) ^ ((r - 1) * (2 * s)) *
      (M : ℝ) ^ (r * (2 * s - 2)) * meanValue r k M := by positivity
  apply (interval_centered_envelope_bound k M t z B hr hs a ha (intervalCenter r k M)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hp) hK) hE

end
end RiemannGaussian.VinogradovKorobovMoment
