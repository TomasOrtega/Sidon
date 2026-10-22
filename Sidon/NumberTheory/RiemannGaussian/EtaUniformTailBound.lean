/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Probability.Moments.ComplexMGF
import Sidon.NumberTheory.RiemannGaussian.EtaAdjacentRatio
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

namespace RiemannGaussian
noncomputable section
open Complex Filter Set Topology
open scoped Classical

def pairedEtaAdjacentBoundary (s : ℂ) (x : ℝ) : ℂ :=
  pairedEtaAdjacentInverse s x * (x : ℂ) ^ (-s)

def pairedEtaAdjacentDefect (s : ℂ) (x : ℝ) : ℂ :=
  (pairedEtaAdjacentInverse s x - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 1 : ℝ) : ℂ) ^ (-s) +
  (pairedEtaAdjacentInverse s (x + 2) - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 2 : ℝ) : ℂ) ^ (-s)

theorem cpow_pair_eq_adjacent_boundary_add_defect (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) =
      pairedEtaAdjacentBoundary s x - pairedEtaAdjacentBoundary s (x + 2) +
        pairedEtaAdjacentDefect s x := by
  have h1 := pairedEtaAdjacentInverse_mul_add s hx hscale
  have h2 := pairedEtaAdjacentInverse_mul_add s
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2
  unfold pairedEtaAdjacentBoundary pairedEtaAdjacentDefect
  linear_combination -h1 + h2

theorem norm_pairedEtaAdjacentBoundary_le {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    ‖pairedEtaAdjacentBoundary s x‖ ≤ x ^ (-s.re) := by
  rw [pairedEtaAdjacentBoundary, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  simpa using mul_le_mul_of_nonneg_right
    (norm_pairedEtaAdjacentInverse_le_one hx hscale) (Real.rpow_nonneg hx.le _)

theorem norm_pairedEtaAdjacentDefect_le {s : ℂ} (hs : 0 ≤ s.re)
    {X x : ℝ} (hX : 0 < X) (hscale : ‖s‖ ≤ X) (hx : X ≤ x) :
    ‖pairedEtaAdjacentDefect s x‖ ≤
      ‖s‖ * X ^ (-s.re) * (pairedEtaStepLog x - pairedEtaStepLog (x + 2)) := by
  have hx0 := hX.trans_le hx
  have h1 := norm_pairedEtaAdjacentInverse_sub_le hs hx0 (hscale.trans hx)
    (show x ≤ x + 1 by linarith)
  have h2 := norm_pairedEtaAdjacentInverse_sub_le hs
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
    (show x + 1 ≤ x + 2 by linarith)
  rw [norm_sub_rev] at h1
  have hp (u : ℝ) (hu : X ≤ u) : ‖(u : ℂ) ^ (-s)‖ ≤ X ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hX.trans_le hu), Complex.neg_re]
    exact Real.rpow_le_rpow_of_nonpos hX hu (neg_nonpos.mpr hs)
  unfold pairedEtaAdjacentDefect
  calc
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog (x + 1))) * X ^ (-s.re) +
        (‖s‖ * (pairedEtaStepLog (x + 1) - pairedEtaStepLog (x + 2))) * X ^ (-s.re) := by
      exact add_le_add
        (mul_le_mul h1 (hp (x + 1) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (mul_le_mul h2 (hp (x + 2) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h2))
    _ = _ := by ring

theorem pairedEtaCorePartialSum_sub_eq_adjacent (s : ℂ) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) -
        pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ) +
      ∑ n ∈ Finset.range M, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := cpow_pair_eq_adjacent_boundary_add_defect s
      (x := ((2 * (M + N) + 1 : ℕ) : ℝ)) (by positivity) (hscale.trans hx)
    have hη : pairedEtaCorePartialSum (M + 1 + N) s =
        pairedEtaCorePartialSum (M + N) s + pairedEtaCoreSummand s (M + N) := by
      rw [show M + 1 + N = (M + N) + 1 by omega]
      exact Finset.sum_range_succ _ _
    rw [hη, Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    simp only [pairedEtaCoreSummand] at h ⊢
    push_cast at h ih ⊢
    rw [show (2 * ((M : ℂ) + N) + 1 + 1 : ℂ) = 2 * ((M : ℂ) + N) + 2 by ring] at h
    linear_combination ih + h

private theorem sum_norm_adjacent_defect_le {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        (pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) -
          pairedEtaStepLog ((2 * (M + N) + 1 : ℕ) : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := norm_pairedEtaAdjacentDefect_le hs (by positivity) hscale hx
    rw [Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    push_cast at h ih ⊢
    calc
      _ ≤ _ := add_le_add ih h
      _ = _ := by ring

private theorem sum_norm_adjacent_defect_le_const {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) := by
  apply (sum_norm_adjacent_defect_le hs N M hscale).trans
  apply mul_le_mul_of_nonneg_left
    (sub_le_self _ (pairedEtaStepLog_bounds (by positivity)).1)
  positivity

theorem summable_pairedEtaAdjacentDefect_tail {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Summable (fun n : ℕ => pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)) := by
  apply Summable.of_norm
  exact summable_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

theorem tsum_norm_pairedEtaAdjacentDefect_tail_le {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑' n : ℕ, ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

private theorem tendsto_adjacent_boundary_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Tendsto (fun M : ℕ => pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun M : ℕ => ((2 * (M + N) + 1 : ℕ) : ℝ) ^ (-s.re))
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · apply Filter.Eventually.of_forall
    intro M
    apply norm_pairedEtaAdjacentBoundary_le (by positivity)
    apply hscale.trans
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
  · exact (tendsto_pairedEtaOddEndpoint_rpow_zero hs).comp (tendsto_add_atTop_nat N)

theorem pairedEtaCore_tail_eq_adjacent {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) +
        ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  have he := ((summable_pairedEtaCoreSummand hs).tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat N)).sub_const (pairedEtaCorePartialSum N s)
  change Tendsto (fun M => pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s)
    atTop (nhds (pairedEtaCore s - pairedEtaCorePartialSum N s)) at he
  simp_rw [pairedEtaCorePartialSum_sub_eq_adjacent s N _ hscale] at he
  have hb := tendsto_adjacent_boundary_zero hs N hscale
  have hr := (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).tendsto_sum_tsum_nat
  have ht := ((tendsto_const_nhds
    (x := pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ))).sub hb).add hr
  simpa using tendsto_nhds_unique he ht

theorem norm_pairedEtaCore_tail_le_two {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      2 * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  let X : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have hl := pairedEtaStepLog_bounds hX
  have hbudget : ‖s‖ * pairedEtaStepLog X ≤ 1 := by
    calc
      _ ≤ X * (1 / X) := mul_le_mul hscale hl.2 hl.1 hX.le
      _ = 1 := by field_simp
  rw [pairedEtaCore_tail_eq_adjacent hs N hscale]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ X ^ (-s.re) + ‖s‖ * X ^ (-s.re) * pairedEtaStepLog X :=
      add_le_add (norm_pairedEtaAdjacentBoundary_le hX hscale)
        ((norm_tsum_le_tsum_norm (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).norm).trans
          (tsum_norm_pairedEtaAdjacentDefect_tail_le hs.le N hscale))
    _ ≤ 2 * X ^ (-s.re) := by
      have h := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hX.le (-s.re))
      nlinarith only [h]

end
end RiemannGaussian
