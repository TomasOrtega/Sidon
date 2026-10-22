/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovCrossMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovInitialExceptional
noncomputable section
open scoped Classical BigOperators
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovCrossMoment
theorem moment_eq_crossCount {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) :
    moment r v = (crossCount (tupleFrequency r v) (tupleFrequency r v) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_natCast, ← crossGram_one]
  have hw : tupleWeight r (fun _ : ι => (1 : ℂ)) = fun _ => 1 := by
    funext x
    simp [tupleWeight]
  have he := even_moment_eq_crossGram r v (fun _ => 1)
  rw [hw] at he
  simpa only [VinogradovPartitionEnergy.polynomial, one_mul, moment] using he

end
end RiemannGaussian.VinogradovInitialExceptional
