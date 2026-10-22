/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.EtaZetaMultiplicitySchwarz
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalCanonical
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalDiscBounds
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalLogDerivative

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h1 : s = 1
  · simp [h1, riemannZeta₁_one]
  · rw [riemannZeta₁_eq_sub_one_mul h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

theorem neg_logDeriv_riemannZeta_eq_pole_sub {s : ℂ} (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s = 1 / (s - 1) - logDeriv riemannZeta₁ s := by
  have hsub := sub_ne_zero.mpr h1
  have hnonzero : riemannZeta₁ s ≠ 0 := by
    rw [riemannZeta₁_eq_sub_one_mul h1]
    exact mul_ne_zero hsub hz
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add h1,
    riemannZeta_eq_inv_sub_mul h1]
  field_simp
  ring

theorem logDeriv_localZetaPoleRemoved_eq (y : ℝ) (z : ℂ) :
    logDeriv (localZetaPoleRemoved y) z = logDeriv riemannZeta₁ (3 / 2 + I * y + z) := by
  have hd : HasDerivAt (localZetaPoleRemoved y) (deriv riemannZeta₁ (3 / 2 + I * y + z)) z := by
    change HasDerivAt (fun w : ℂ ↦ riemannZeta₁ (3 / 2 + I * y + w)) _ z
    simpa only [Function.comp_def, mul_one, id_eq] using
      (differentiable_riemannZeta₁ (3 / 2 + I * y + z)).hasDerivAt.comp z
        ((hasDerivAt_id z).const_add (3 / 2 + I * y))
  simp only [logDeriv_apply, hd.deriv, localZetaPoleRemoved]

theorem localZetaDivisor_re_lt_neg_half (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0) :
    i.re < -(1 / 2 : ℝ) := by
  have hf := localZetaPoleRemoved_eq_zero_of_divisor_ne_zero y hi
  by_contra h
  have hs : 1 ≤ (3 / 2 + I * (y : ℂ) + i).re := by simp; linarith
  exact riemannZeta₁_ne_zero_of_one_le_re hs hf

end

end RiemannGaussian
