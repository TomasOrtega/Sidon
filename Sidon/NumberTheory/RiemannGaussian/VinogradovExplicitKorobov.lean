/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.NumberTheory.Bertrand
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment

namespace RiemannGaussian.VinogradovExplicitKorobov
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
theorem abs_phaseCoefficients (k : ℕ) (t : ℝ) {z : ℝ} (hz : 0 < z) (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k t z j| =
      |t| / ((j.val + 1) * z ^ (j.val + 1)) / (2 * Real.pi) := by
  have hd : 0 < ((j.val : ℝ) + 1) * z ^ (j.val + 1) := by positivity
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [VinogradovKorobovMoment.phaseCoefficients, abs_div]
  rw [abs_of_pos hd, abs_of_pos hp, abs_mul]
  simp

end
end RiemannGaussian.VinogradovExplicitKorobov
