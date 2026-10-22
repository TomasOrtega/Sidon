/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.AnalyticDiscBoundaryMoment
import Sidon.NumberTheory.RiemannGaussian.SignedCircleProjection

namespace RiemannGaussian.AnalyticDiscSignedBoundary
noncomputable section
open Complex Metric Set MeromorphicOn RiemannGaussian.AnalyticDiscBoundaryMoment RiemannGaussian.AnalyticDiscSignedDerivative
theorem neg_moment_re_le {f : ℂ → ℂ} {R B C : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0)
    (hleft : ∀ z ∈ sphere 0 R, z.re ≤ 0 → Real.log ‖f z‖ ≤ B)
    (hright : ∀ z ∈ sphere 0 R, 0 ≤ z.re → -Real.log ‖f z‖ ≤ C) :
    (-moment f R).re ≤ 2 * (B + C) / (Real.pi * R) := by
  have hlog : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (hf.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz)))
  rw [neg_moment_re hR hf hne]
  apply (mul_le_mul_of_nonneg_left
    (SignedCircleProjection.signed_average_le hR.le hlog hleft hright)
    (by positivity : 0 ≤ 2 / R ^ 2)).trans_eq
  field_simp

end
end RiemannGaussian.AnalyticDiscSignedBoundary
