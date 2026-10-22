/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.MetricSpace.Thickening
import Sidon.NumberTheory.RiemannGaussian.EtaZetaMultiplicitySchwarz
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

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
