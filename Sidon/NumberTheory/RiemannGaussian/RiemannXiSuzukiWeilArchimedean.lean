module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Sidon.NumberTheory.RiemannGaussian.GaussianDigammaGauss

@[expose] public section

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval LSeries.notation Topology lp

namespace RiemannGaussian

noncomputable section

def suzukiWeilDigammaDifferenceSummand
    (a b : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + b)⁻¹ - ((n : ℂ) + a)⁻¹

theorem summable_norm_suzukiWeilDigammaDifferenceSummand
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun n ↦ ‖suzukiWeilDigammaDifferenceSummand a b n‖) := by
  let c : ℝ := min 1 (min a.re b.re)
  have hc : 0 < c := by
    exact lt_min one_pos (lt_min ha hb)
  have hcOne : c ≤ 1 := min_le_left _ _
  have hcA : c ≤ a.re :=
    (min_le_right (1 : ℝ) (min a.re b.re)).trans (min_le_left _ _)
  have hcB : c ≤ b.re :=
    (min_le_right (1 : ℝ) (min a.re b.re)).trans (min_le_right _ _)
  have hdenA (n : ℕ) :
      c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + a‖ := by
    calc
      c * ((n : ℝ) + 1) = c * n + c := by ring
      _ ≤ (n : ℝ) + a.re := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hcn : c * (n : ℝ) ≤ 1 * n :=
          mul_le_mul_of_nonneg_right hcOne hn
        linarith
      _ = ((n : ℂ) + a).re := by simp
      _ ≤ ‖(n : ℂ) + a‖ := Complex.re_le_norm _
  have hdenB (n : ℕ) :
      c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + b‖ := by
    calc
      c * ((n : ℝ) + 1) = c * n + c := by ring
      _ ≤ (n : ℝ) + b.re := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hcn : c * (n : ℝ) ≤ 1 * n :=
          mul_le_mul_of_nonneg_right hcOne hn
        linarith
      _ = ((n : ℂ) + b).re := by simp
      _ ≤ ‖(n : ℂ) + b‖ := Complex.re_le_norm _
  have hbase : Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hp
  apply (hbase.mul_left (‖a - b‖ / c ^ 2)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro n
  have hnPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcNPos : 0 < c * ((n : ℝ) + 1) := mul_pos hc hnPos
  have hA0 : (n : ℂ) + a ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt (hcNPos.trans_le (hdenA n)))
  have hB0 : (n : ℂ) + b ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt (hcNPos.trans_le (hdenB n)))
  have hterm :
      suzukiWeilDigammaDifferenceSummand a b n =
        (a - b) / (((n : ℂ) + b) * ((n : ℂ) + a)) := by
    unfold suzukiWeilDigammaDifferenceSummand
    field_simp [hA0, hB0]
    ring
  have hprod :
      (c * ((n : ℝ) + 1)) ^ 2 ≤
        ‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖ := by
    calc
      (c * ((n : ℝ) + 1)) ^ 2 =
          (c * ((n : ℝ) + 1)) *
            (c * ((n : ℝ) + 1)) := by ring
      _ ≤ ‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖ :=
        mul_le_mul (hdenB n) (hdenA n) hcNPos.le (norm_nonneg _)
  rw [hterm, norm_div, norm_mul]
  calc
    ‖a - b‖ / (‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖) ≤
        ‖a - b‖ / (c * ((n : ℝ) + 1)) ^ 2 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hcNPos)
        hprod
    _ = (‖a - b‖ / c ^ 2) *
        (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hc]

theorem hasSum_suzukiWeilDigammaDifferenceSummand
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    HasSum (suzukiWeilDigammaDifferenceSummand a b)
      (Complex.digamma a - Complex.digamma b) := by
  have hdiff := (Complex.digamma_tendsto_euler ha).sub
    (Complex.digamma_tendsto_euler hb)
  have hshift : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range (n + 1),
        suzukiWeilDigammaDifferenceSummand a b j)
      atTop (nhds (Complex.digamma a - Complex.digamma b)) := by
    apply hdiff.congr'
    filter_upwards with n
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [suzukiWeilDigammaDifferenceSummand, add_comm]
  have hpartial : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range n,
        suzukiWeilDigammaDifferenceSummand a b j)
      atTop (nhds (Complex.digamma a - Complex.digamma b)) := by
    exact (tendsto_add_atTop_iff_nat 1).mp
      (by simpa [Nat.add_comm] using hshift)
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_suzukiWeilDigammaDifferenceSummand ha hb)).2 hpartial

end

end RiemannGaussian
