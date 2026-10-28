module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Sidon.NumberTheory.RiemannGaussian.DirichletPowerCoefficients
public import Sidon.NumberTheory.RiemannGaussian.LogarithmicDerivativeFamily
public import Sidon.NumberTheory.RiemannGaussian.UniformDirichletPowerBound

@[expose] public section

namespace RiemannGaussian.DirichletBlockPowerProfile
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerCoefficients RiemannGaussian.DirichletDyadicBlocks
open RiemannGaussian.LogarithmicDerivativeFamily
def exactProfile (k : ℕ) (σ t X : ℝ) : ℝ :=
  128 * factor k ^ alpha k * t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) +
    32 * factor k ^ (-alpha k) * t ^ (-alpha k) *
      X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k)

def profile (k : ℕ) (σ t X : ℝ) : ℝ :=
  256 * t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) +
    64 * t ^ (-alpha k) * X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k)

theorem profile_nonneg (k : ℕ) (σ : ℝ) {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) :
    0 ≤ profile k σ t X := by
  unfold profile
  positivity

theorem exactProfile_le (k : ℕ) (σ : ℝ) {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) :
    exactProfile k σ t X ≤ profile k σ t X := by
  have h1 := mul_le_mul_of_nonneg_right (factor_positive_power_le_two k)
    (show 0 ≤ t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (factor_negative_power_le_two k)
    (show 0 ≤ t ^ (-alpha k) * X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k) by positivity)
  unfold exactProfile profile
  nlinarith

theorem exact_bound (k j : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im) :
    ‖block s j‖ ≤ exactProfile k s.re s.im ((2 ^ j : ℕ) : ℝ) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have h := UniformDirichletPowerBound.uniform_bound k hσ ht hX (2 ^ j) (2 ^ j)
    le_rfl (by dsimp [X]; ring_nf; exact le_rfl)
  rw [weight_eq_rpow s.re (by positivity)] at h
  change ‖block s j‖ ≤ 32 * (4 * X * lowerScale s.im X k ^ alpha k +
    X ^ beta k * lowerScale s.im X k ^ (-alpha k)) * X ^ (-s.re) at h
  have hlead : X ^ (1 - s.re - ((k : ℝ) + 2) * alpha k) =
      X * X ^ (-((k : ℝ) + 2) * alpha k) * X ^ (-s.re) := by
    rw [show 1 - s.re - ((k : ℝ) + 2) * alpha k =
      1 + (-((k : ℝ) + 2) * alpha k) + (-s.re) by ring,
      Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]
  have herr : X ^ (beta k - s.re + ((k : ℝ) + 2) * alpha k) =
      X ^ beta k * X ^ (-((k : ℝ) + 2) * (-alpha k)) * X ^ (-s.re) := by
    rw [show beta k - s.re + ((k : ℝ) + 2) * alpha k =
      beta k + (-((k : ℝ) + 2) * (-alpha k)) + (-s.re) by ring,
      Real.rpow_add hX, Real.rpow_add hX]
  apply h.trans_eq
  rw [scale_power k ht hX (alpha k), scale_power k ht hX (-alpha k)]
  change _ = exactProfile k s.re s.im X
  unfold exactProfile
  rw [hlead, herr]
  ring

theorem bound (k j : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im) :
    ‖block s j‖ ≤ profile k s.re s.im ((2 ^ j : ℕ) : ℝ) :=
  (exact_bound k j hσ ht).trans (exactProfile_le k s.re ht.le (by positivity))

end
end RiemannGaussian.DirichletBlockPowerProfile
