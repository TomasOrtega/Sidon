module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

namespace RiemannGaussian

noncomputable section

open Filter
open scoped Topology

lemma logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnotPole : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    nlinarith
  have hGamma : Complex.Gamma (s / 2) ≠ 0 := by
    exact Complex.Gamma_ne_zero hnotPole
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hGammaDiff :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hnotPole).comp s (by fun_prop)
  have hexponent : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s :=
    (hasDerivAt_id s).neg.div_const 2
  have hpowDiff :
      DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hexponent.differentiableAt.const_cpow (Or.inl hpi)
  have hpowLog :
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
        -Complex.log Real.pi / 2 := by
    rw [logDeriv_apply,
      Complex.deriv_const_cpow hexponent.differentiableAt (Real.pi : ℂ),
      hexponent.deriv]
    field_simp [hpow]
  have hGammaLog :
      logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
        Complex.digamma (s / 2) / 2 := by
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) =
        Complex.Gamma ∘ (fun z : ℂ => z / 2) by rfl,
      logDeriv_comp (Complex.differentiableAt_Gamma (s / 2) hnotPole)
        (x := s) (g := fun z : ℂ => z / 2) (by fun_prop)]
    rw [← Complex.digamma_def]
    simp
    ring
  change logDeriv
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s = _
  rw [logDeriv_fun_mul s hpow hGamma]
  · rw [hpowLog, hGammaLog]
  · exact hpowDiff
  · exact hGammaDiff

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℝ s ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  have hre := congrArg Complex.re hn
  norm_num at hre
  nlinarith

lemma differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnotPole : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    nlinarith
  have hexponent : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by
    fun_prop
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hexponent.const_cpow (Or.inl hpi)
  have hGamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hnotPole).comp s (by fun_prop)
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  exact hpow.mul hGamma

end

end RiemannGaussian
