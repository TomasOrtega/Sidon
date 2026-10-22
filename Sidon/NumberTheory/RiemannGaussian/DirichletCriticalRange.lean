/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters

namespace RiemannGaussian.DirichletCriticalRange
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.DirichletBlockPowerProfile
theorem profile_on_line (k : ℕ) (t X : ℝ) :
    profile k (line k) t X = 256 * t ^ alpha k + 64 * t ^ (-alpha k) * X ^ slope k := by
  unfold profile line
  rw [show 1 - (1 - ((k : ℝ) + 2) * alpha k) - ((k : ℝ) + 2) * alpha k = 0 by ring,
    Real.rpow_zero, mul_one]
  rw [show beta k - (1 - ((k : ℝ) + 2) * alpha k) + ((k : ℝ) + 2) * alpha k =
    slope k by unfold beta DirichletPowerParameters.slope; ring]

theorem profile_le_on_range (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X)
    (hupper : X ≤ t ^ transition k) : profile k (line k) t X ≤ 320 * t ^ alpha k := by
  have hp := Real.rpow_le_rpow hX.le hupper (slope_pos k).le
  rw [← Real.rpow_mul ht.le, transition_balance] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le (-alpha k))
  have he : t ^ (-alpha k) * t ^ (2 * alpha k) = t ^ alpha k := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [he] at hm
  rw [profile_on_line]
  nlinarith

end
end RiemannGaussian.DirichletCriticalRange
