module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.NumberTheory.LSeries.Deriv
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram

@[expose] public section

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

def zetaPrimeExpWeight (σ : ℝ) (m : ℕ) : ℝ := Real.exp (-σ * Real.log m)

theorem norm_zetaPrimeFeature (s : ℂ) (m : ℕ) :
    ‖zetaPrimeFeature s m‖ = zetaPrimeExpWeight s.re m := by
  simp only [zetaPrimeFeature, zetaPrimeExpWeight, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

end

end RiemannGaussian
