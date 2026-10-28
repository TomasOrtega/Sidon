module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralUpperContourProjection

@[expose] public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem SuzukiXiUpperContourBottomAdmissible.mono
    {T eta eta' : ℝ}
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (heta' : 0 < eta') (hle : eta' ≤ eta) :
    SuzukiXiUpperContourBottomAdmissible T eta' := by
  refine ⟨heta', hle.trans_lt heta.2.1, ?_⟩
  intro rho hrho hupper
  exact hle.trans_lt (heta.2.2 rho hrho hupper)

end

end RiemannGaussian
