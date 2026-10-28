module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.NumberTheory.Bertrand
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment

@[expose] public section

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
