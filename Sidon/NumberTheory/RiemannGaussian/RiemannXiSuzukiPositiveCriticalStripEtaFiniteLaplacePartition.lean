/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaFiniteLaplacePartition (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp (-s * t)

theorem pairedEtaCoreSummand_eq_mul_logLaplaceInterval
    (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ t : ℝ in
        Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp (-s * t) := by
  by_cases hs : s = 0
  · subst s
    simp [pairedEtaCoreSummand]
  · have hoddNonneg : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      positivity
    have hevenNonneg : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
      positivity
    have hodd : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    have heven : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)
    have hoddPow :
        Complex.exp (-s * Real.log (2 * n + 1)) =
          ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hodd,
        ← Complex.ofReal_log hoddNonneg]
      congr 1
      push_cast
      ring
    have hevenPow :
        Complex.exp (-s * Real.log (2 * n + 2)) =
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero heven,
        ← Complex.ofReal_log hevenNonneg]
      congr 1
      push_cast
      ring
    rw [integral_exp_mul_complex (c := -s) (neg_ne_zero.mpr hs)]
    rw [hoddPow, hevenPow]
    unfold pairedEtaCoreSummand
    field_simp [hs]
    simp only [Nat.mul_comm]
    abel

theorem pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition
    (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s =
      s * pairedEtaFiniteLaplacePartition N s := by
  unfold pairedEtaCorePartialSum pairedEtaFiniteLaplacePartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n

theorem pairedEtaFiniteLaplaceKernel_re (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      Real.exp (-sigma * t) * Real.cos (y * t) := by
  rw [Complex.exp_re]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem pairedEtaFiniteLaplaceKernel_im (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im =
      -(Real.exp (-sigma * t) * Real.sin (y * t)) := by
  rw [Complex.exp_im]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem pairedEtaFiniteLaplaceInterval_re
    (sigma y : ℝ) (n : ℕ) :
    (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t) * Real.cos (y * t) := by
  have hcont : Continuous
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      MeasureSpace.volume
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2)) :=
    hcont.intervalIntegrable
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2))
  have hre :
      (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re) =
        (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re := by
    simpa using intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  apply intervalIntegral.integral_congr
  intro t _
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem pairedEtaFiniteLogInterval_pos (n : ℕ) :
    Real.log (2 * n + 1) < Real.log (2 * n + 2) := by
  apply Real.log_lt_log
  · positivity
  · exact_mod_cast (show 2 * n + 1 < 2 * n + 2 by omega)

end

end RiemannGaussian
