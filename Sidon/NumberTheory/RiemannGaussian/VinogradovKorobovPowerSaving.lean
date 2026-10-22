/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianKernel
import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentReduction
import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovKorobovPowerSaving
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
open RiemannGaussian.VinogradovResonanceScaling
theorem reciprocal_support_cost (k r : ℕ) (hr : 0 < r) {M : ℕ} (hM : 0 < M) :
    VinogradovGaussianKernel.supportCost (fun j : Fin k => reciprocalScale r M (j.val + 1))
      (VinogradovMomentReduction.frequencySupport (VinogradovShiftedMoment.tupleFrequency r
        (fun b : Fin M => VinogradovMeanValue.monomialFrequency k (b.val + 1)))) = (k : ℝ) * Real.pi := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [VinogradovKorobovMoment.interval_origin_cost_eq r k hM
    (fun j => (reciprocalScale_pos hr hMpos (j.val + 1)).le)]
  have he (j : Fin k) : Real.pi * reciprocalScale r M (j.val + 1) *
      ((r : ℝ) * (M : ℝ) ^ (j.val + 1)) ^ 2 = Real.pi := by
    unfold reciprocalScale
    field_simp
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end RiemannGaussian.VinogradovKorobovPowerSaving
