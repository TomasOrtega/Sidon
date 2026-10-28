module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.MetricSpace.Thickening
public import Sidon.NumberTheory.RiemannGaussian.EtaZetaMultiplicitySchwarz
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

@[expose] public section

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

def suzukiGammaShiftNumerator (s : ℂ) : ℂ :=
  riemannZeta₁ s / ((s + 2) * (s + 4))

def suzukiGammaShiftFactor (s : ℂ) : ℂ :=
  (-8 * (Real.pi : ℂ) ^ 3) * Complex.Gammaℝ (s + 6)

private lemma shift_ne_zero {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a) :
    s + (a : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)

theorem suzukiGammaShiftFactor_eq_polynomial {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s = -s * (s + 2) * (s + 4) * Complex.Gammaℝ s := by
  have hs0 := ne_zero_of_re_pos hs
  have hs2 : s + 2 ≠ 0 := by simpa using shift_ne_zero hs (a := 2) (by norm_num)
  have hs4 : s + 4 ≠ 0 := by simpa using shift_ne_zero hs (a := 4) (by norm_num)
  unfold suzukiGammaShiftFactor
  rw [show s + 6 = (s + 4) + 2 by ring, Complex.Gammaℝ_add_two hs4,
    show s + 4 = (s + 2) + 2 by ring, Complex.Gammaℝ_add_two hs2,
    Complex.Gammaℝ_add_two hs0]
  field_simp
  ring

theorem suzukiGammaShiftFactor_mul_numerator {s : ℂ} (hs : 0 < s.re) :
    suzukiGammaShiftFactor s * suzukiGammaShiftNumerator s = riemannXi s := by
  rw [suzukiGammaShiftFactor_eq_polynomial hs, suzukiGammaShiftNumerator]
  have hs2 : s + 2 ≠ 0 := by simpa using shift_ne_zero hs (a := 2) (by norm_num)
  have hs4 : s + 4 ≠ 0 := by simpa using shift_ne_zero hs (a := 4) (by norm_num)
  by_cases h1 : s = 1
  · subst s
    norm_num [riemannXi_one, riemannZeta₁_one, Complex.Gammaℝ_one]
  · rw [riemannZeta₁_eq_sub_one_mul h1, riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs h1]
    field_simp [hs2, hs4]
    ring

end
end RiemannGaussian
