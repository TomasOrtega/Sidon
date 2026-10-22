/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem NontrivialZetaZero.im_ne_zero_of_eta_mass (rho : NontrivialZetaZero) : rho.1.im ≠ 0 := by
  intro him
  have h := (pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho).1
  rw [him] at h
  have hp := pairedEtaTiltedCosineMoment_zero_pos rho.1.re (NontrivialZetaZero.zero_lt_re rho)
  linarith

end

end RiemannGaussian
