/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCriticalKorobov
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianCost
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovPowerSaving
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovRectanglePowerSaving
import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance
import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

namespace RiemannGaussian.VinogradovRelativeResonance
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment RiemannGaussian.VinogradovKorobovMoment
open RiemannGaussian.VinogradovKorobovBilinearPhase RiemannGaussian.VinogradovCriticalKorobov
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovResonanceScaling
open RiemannGaussian.VinogradovRectangleResonance RiemannGaussian.VinogradovRectanglePowerSaving
open RiemannGaussian.VinogradovKorobovPowerSaving
theorem product_moment_bound_with_defect (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (k + 1) * k ≤ M)
    (C eps : ℝ) (hC : 0 ≤ C)
    (hJ : meanValue ((k + 1) * k) k M ≤ C * (M : ℝ) ^
      (2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps))
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    let r := (k + 1) * k
    ‖∑ b : Fin M, ∑ c ∈ B, polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * r) ≤
      (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        (M : ℝ) ^ (4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps) := by
  let r := (k + 1) * k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := hr
  have hr2 : 2 ≤ 2 * r := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  let lam := 2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
  let a (j : Fin k) := reciprocalScale r M (j.val + 1)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hsecond := (finite_moment_le_interval r k M B hB).trans hJ
  have hK : 0 ≤ moment r (fun b : B => monomialFrequency k b.val) :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hJ0 : 0 ≤ meanValue r k M :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hE := resonanceEnvelope_nonneg r ha (phaseCoefficients k t z)
    (fun b : B => monomialFrequency k b.val)
  have hcard : (B.card : ℝ) ≤ M := by
    apply Nat.cast_le.mpr
    have hc := Finset.card_le_card (show B ⊆ Finset.Icc 1 M from
      fun b hb => Finset.mem_Icc.mpr (hB b hb))
    simpa using hc
  have hbase := interval_quarter_envelope_bound k (by omega : 0 < M) t z B hr1 hr1 a ha
  dsimp only at hbase
  rw [reciprocal_support_cost k r hr (by omega : 0 < M)] at hbase
  have hres := VinogradovGaussianCost.actual_gaussian_resonance_le k hk M hM hrM t z
    htlo hthi hzlo hzhi B (fun b hb => (hB b hb).2)
  let A := (r - 1) * (2 * r)
  let F := r * (2 * r - 2)
  let Q := k * (k + 1) - rectangleSaving k
  have hAr : (A : ℝ) = 2 * (r : ℝ) ^ 2 - 2 * r := by
    dsimp only [A]
    rw [Nat.cast_mul, Nat.cast_sub hr1]
    push_cast
    ring
  have hFr : (F : ℝ) = 2 * (r : ℝ) ^ 2 - 2 * r := by
    dsimp only [F]
    rw [Nat.cast_mul, Nat.cast_sub hr2]
    push_cast
    ring
  have hQr : (Q : ℝ) = (k : ℝ) * ((k : ℝ) + 1) - (rectangleSaving k : ℝ) := by
    dsimp only [Q]
    rw [Nat.cast_sub (rectangleSaving_le_dimension k)]
    push_cast
    ring
  have hrr : (r : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by dsimp only [r]; push_cast; ring
  have hexp : (A : ℝ) + F + lam + lam + Q =
      4 * (r : ℝ) ^ 2 - (rectangleSaving k : ℝ) + 2 * eps := by
    rw [hAr, hFr, hQr]
    dsimp only [lam]
    nlinarith only [hrr]
  apply hbase.trans
  calc
    _ ≤ (M : ℝ) ^ A * (M : ℝ) ^ F * (C * (M : ℝ) ^ lam) *
        Real.exp ((k : ℝ) * Real.pi / 4) * (C * (M : ℝ) ^ lam) *
        resonanceEnvelope r a (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val) := by
      gcongr
    _ = C ^ 2 * ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam) *
        (Real.exp ((k : ℝ) * Real.pi / 4) *
          resonanceEnvelope r a (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val)) := by ring
    _ ≤ C ^ 2 * ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam) *
        ((2 : ℝ) ^ (9 * k ^ 2) * (M : ℝ) ^ Q) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ = (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) *
        ((M : ℝ) ^ A * (M : ℝ) ^ F * (M : ℝ) ^ lam * (M : ℝ) ^ lam * (M : ℝ) ^ Q) := by ring
    _ = (C ^ 2 * (2 : ℝ) ^ (9 * k ^ 2)) * (M : ℝ) ^ ((A : ℝ) + F + lam + lam + Q) := by
      rw [← Real.rpow_natCast (M : ℝ) A, ← Real.rpow_natCast (M : ℝ) F,
        ← Real.rpow_natCast (M : ℝ) Q, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos,
        ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
    _ = _ := by rw [hexp]

end
end RiemannGaussian.VinogradovRelativeResonance
