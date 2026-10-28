module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.MeanInequalities
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

@[expose] public section

namespace RiemannGaussian

noncomputable section

open MeromorphicOn Metric Set
theorem jensen_riemannXi_divisor_le_threeHalves
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM :
      1 ≤ Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA)
      (Real.rpow_nonneg (by positivity) _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

end

end RiemannGaussian
