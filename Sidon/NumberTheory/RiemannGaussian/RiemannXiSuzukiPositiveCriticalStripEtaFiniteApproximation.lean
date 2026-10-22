/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaCorePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaCoreSummand s n

end

end RiemannGaussian
