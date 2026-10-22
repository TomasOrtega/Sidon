/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Periodic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.MetricSpace.Contracting
import Sidon.NumberTheory.RiemannGaussian.GaussianCompletedLogDerivative
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry
import Sidon.NumberTheory.RiemannGaussian.RiemannXiGlobalLogDerivative
import Sidon.NumberTheory.RiemannGaussian.RosserSchoenfeldEulerConstant
import Sidon.NumberTheory.RiemannGaussian.SuzukiGammaShift

open Complex Filter Topology
namespace RiemannGaussian.RosserSchoenfeldZeroMass
noncomputable section
open RiemannGaussian.RosserSchoenfeldEulerConstant
theorem xi_factor {s : ℂ} (hs : 0 < s.re) :
    riemannXi s = -s * Complex.Gammaℝ s * riemannZeta₁ s := by
  have h2 : s + 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h4 : s + 4 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  rw [← suzukiGammaShiftFactor_mul_numerator hs,
    suzukiGammaShiftFactor_eq_polynomial hs, suzukiGammaShiftNumerator]
  field_simp

theorem xi_log_one : logDeriv riemannXi 1 =
    1 + (Real.eulerMascheroniConstant : ℂ) / 2 - Complex.log 2 - Complex.log Real.pi / 2 := by
  have he : riemannXi =ᶠ[𝓝 (1 : ℂ)]
      (fun s => -s * Complex.Gammaℝ s * riemannZeta₁ s) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds (show 0 < (1 : ℂ).re by norm_num)] with s hs
    exact xi_factor hs
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_fun_mul (f := fun s : ℂ => -s * Complex.Gammaℝ s) (g := riemannZeta₁) (1 : ℂ) (by simp [Complex.Gammaℝ_one]) (by simp)
      ((differentiableAt_id.neg).mul (differentiableAt_Gammaℝ_of_re_pos (by norm_num)))
      (differentiable_riemannZeta₁ 1),
    logDeriv_fun_mul (f := fun s : ℂ => -s) (g := Complex.Gammaℝ) (1 : ℂ) (by norm_num) (by simp [Complex.Gammaℝ_one])
      (by fun_prop) (differentiableAt_Gammaℝ_of_re_pos (by norm_num)),
    logDeriv_Gammaℝ (by norm_num)]
  rw [Complex.digamma_one_half]
  have hn : logDeriv (fun s : ℂ => -s) 1 = 1 := by simp [logDeriv_apply]
  have hz : logDeriv riemannZeta₁ 1 = (Real.eulerMascheroniConstant : ℂ) := by simp [logDeriv_apply]
  rw [hn, hz]
  ring

def poisson (ρ : NontrivialZetaZero) : ℝ :=
  (1 - ρ.1.re) / ((1 - ρ.1.re)^2 + ρ.1.im^2) +
    ρ.1.re / (ρ.1.re^2 + ρ.1.im^2)

theorem hasSum_poisson : HasSum
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ) * poisson ρ)
    massConstant := by
  have hh := Complex.hasSum_re (hasSum_zetaLogDeriv_reflection
    (s := 1) (by simp [riemannXi_one]))
  rw [xi_log_one] at hh
  convert hh using 1
  · ext ρ
    rw [zetaLogDerivDifferenceSummand_reflection_re]
    simp [poisson, Complex.normSq_apply, pow_two]
  · norm_num [massConstant, Complex.mul_re, Complex.log_re,
      Complex.norm_real, abs_of_pos Real.pi_pos]
    ring

theorem poisson_lower (ρ : NontrivialZetaZero) :
    1 / (1 + ρ.1.im ^ 2) ≤ poisson ρ := by
  have hb0 := NontrivialZetaZero.zero_lt_re ρ
  have hb1 := NontrivialZetaZero.re_lt_one ρ
  have hleft : 0 < (1 - ρ.1.re) ^ 2 := sq_pos_of_pos (by linarith)
  have hright : 0 < ρ.1.re ^ 2 := sq_pos_of_pos hb0
  have ha : (1 - ρ.1.re) / (1 + ρ.1.im ^ 2) ≤
      (1 - ρ.1.re) / ((1 - ρ.1.re)^2 + ρ.1.im^2) :=
    div_le_div_of_nonneg_left (by linarith) (by nlinarith [sq_nonneg ρ.1.im])
      (by nlinarith)
  have hb : ρ.1.re / (1 + ρ.1.im ^ 2) ≤
      ρ.1.re / (ρ.1.re^2 + ρ.1.im^2) :=
    div_le_div_of_nonneg_left hb0.le (by nlinarith [sq_nonneg ρ.1.im]) (by nlinarith)
  have hh := add_le_add ha hb
  calc
    1 / (1 + ρ.1.im ^ 2) =
        (1 - ρ.1.re) / (1 + ρ.1.im ^ 2) + ρ.1.re / (1 + ρ.1.im ^ 2) := by ring
    _ ≤ poisson ρ := hh

theorem norm_square_mass_summable :
    Summable (fun ρ : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ.1 : ℂ)‖ ^ 2) := by
  have hzero : (0 : ℂ) ∉ riemannZetaZeros := by
    simp only [mem_riemannZetaZeros, riemannZeta_zero]
    norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (isClosed_riemannZetaZeros.isOpen_compl.mem_nhds hzero)
  have hnorm (ρ : NontrivialZetaZero) : ε ≤ ‖(ρ.1 : ℂ)‖ := by
    by_contra hh
    have hn : ρ.1 ∈ Metric.ball (0 : ℂ) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hh
    exact (hball hn) ρ.2.1
  let D : ℝ := (1 + ε ^ 2) / ε ^ 2
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply (hasSum_poisson.summable.mul_left D).of_nonneg_of_le (fun _ => by positivity)
  intro ρ
  have hn : 0 < ‖(ρ.1 : ℂ)‖ ^ 2 := sq_pos_of_pos (hε.trans_le (hnorm ρ))
  have hγ : ρ.1.im ^ 2 ≤ ‖(ρ.1 : ℂ)‖ ^ 2 := by
    calc
      _ = |ρ.1.im| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  have hsq : ε ^ 2 ≤ ‖(ρ.1 : ℂ)‖ ^ 2 := by
    nlinarith [hnorm ρ, norm_nonneg ρ.1]
  have hden : 1 + ρ.1.im ^ 2 ≤ D * ‖(ρ.1 : ℂ)‖ ^ 2 := by
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hεsq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hγ hεsq.le]
  have hg : 0 < 1 + ρ.1.im ^ 2 := by positivity
  have hrecip : 1 / ‖(ρ.1 : ℂ)‖ ^ 2 ≤ D / (1 + ρ.1.im ^ 2) :=
    (div_le_div_iff₀ hn hg).mpr (by simpa only [one_mul] using hden)
  calc
    (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ.1 : ℂ)‖ ^ 2 = (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / ‖(ρ.1 : ℂ)‖ ^ 2) := by ring
    _ ≤ (analyticZetaZeroMultiplicity ρ : ℝ) * (D / (1 + ρ.1.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg _)
    _ = D * ((analyticZetaZeroMultiplicity ρ : ℝ) / (1 + ρ.1.im ^ 2)) := by ring
    _ ≤ D * ((analyticZetaZeroMultiplicity ρ : ℝ) * poisson ρ) := by
      apply mul_le_mul_of_nonneg_left _ hD
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left (poisson_lower ρ) (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ analyticZetaZeroMultiplicity ρ)

end
end RiemannGaussian.RosserSchoenfeldZeroMass
