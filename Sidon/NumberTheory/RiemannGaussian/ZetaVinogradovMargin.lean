module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaLocalResidualLog
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovLocalDisc

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovMargin
noncomputable section
open RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection RiemannGaussian.ZetaVinogradovLocalDisc
def reserve (n : ℕ) (t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 + profile n t + profile n (2 * t) + Real.log (1 / delta n) + 20

def width (n : ℕ) (t : ℝ) : ℝ := delta n / (4096 * reserve n t)

theorem reserve_bounds {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    20 ≤ reserve n t ∧ profile n t ≤ reserve n t ∧ profile n (2 * t) ≤ reserve n t ∧
      Real.log (1 / delta n) + 20 ≤ reserve n t ∧
        1344 * localZetaLogHeight 0 ≤ reserve n t := by
  have hD : 0 ≤ 1344 * localZetaLogHeight 0 := by linarith [two_lt_localZetaLogHeight 0]
  have h1 := profile_nonneg hn t
  have h2 := profile_nonneg hn (2 * t)
  have hi : 0 ≤ Real.log (1 / delta n) := Real.log_nonneg
    ((one_le_div (delta_pos n)).mpr (by linarith [delta_le n]))
  unfold reserve
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end RiemannGaussian.ZetaVinogradovMargin
