/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

lemma pairedEtaCoreSummand_conj (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
  unfold pairedEtaCoreSummand
  rw [map_sub]
  congr 1
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))

lemma pairedEtaCore_conj (s : ℂ) :
    pairedEtaCore ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pairedEtaCore s) := by
  unfold pairedEtaCore
  calc
    ∑' n : ℕ, pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
        ∑' n : ℕ, (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
      apply tsum_congr
      exact pairedEtaCoreSummand_conj s
    _ = (starRingEnd ℂ) (∑' n : ℕ, pairedEtaCoreSummand s n) :=
      (Complex.conj_tsum _).symm

lemma two_cpow_neg_conj (s : ℂ) :
    (2 : ℂ) ^ (-((starRingEnd ℂ) s)) =
      (starRingEnd ℂ) ((2 : ℂ) ^ (-s)) := by
  simpa only [map_neg, map_ofNat] using
    (Complex.cpow_conj (2 : ℂ) (-s)
      (by
        change (((2 : ℕ) : ℂ)).arg ≠ Real.pi
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm))

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im < 0) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  have h := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := (starRingEnd ℂ) s) (by simpa using hsre) (by simpa using hsim)
  have hc := congrArg (starRingEnd ℂ) h
  simpa [pairedEtaCore_conj, two_cpow_neg_conj,
    starRingEnd_self_apply, map_ofNat] using hc

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im = 0) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  let t : Set ℂ := pairedEtaUpperRightDomain ∪ {s}
  have heq : Set.EqOn pairedEtaCore rhs pairedEtaUpperRightDomain := by
    intro w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hw.1 hw.2
  have htpos : t ⊆ {w : ℂ | 0 < w.re} := by
    intro w hw
    rcases hw with hw | hw
    · exact hw.1
    · simpa only [mem_singleton_iff] using hw ▸ hsre
  have hlhs : ContinuousOn pairedEtaCore t :=
    (analyticOnNhd_pairedEtaCore.mono htpos).continuousOn
  have hrhs : ContinuousOn rhs t := by
    intro w hw
    have hwone : w ≠ 1 := by
      rcases hw with hw | hw
      · intro h
        subst w
        simpa [pairedEtaUpperRightDomain] using hw.2
      · simpa only [mem_singleton_iff] using hw ▸ hsone
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    exact
      (hfactor.mul
        (differentiableAt_riemannZeta hwone)).continuousAt.continuousWithinAt
  have hsclosure : s ∈ closure pairedEtaUpperRightDomain := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨s + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · constructor
      · simpa [pairedEtaUpperRightDomain] using hsre
      · simp [hsim]
        positivity
    · rw [dist_eq_norm]
      simp [Real.norm_eq_abs, abs_of_pos hε]
      linarith
  have htclosure : t ⊆ closure pairedEtaUpperRightDomain := by
    intro w hw
    rcases hw with hw | hw
    · exact subset_closure hw
    · simpa only [mem_singleton_iff] using hw ▸ hsclosure
  have hall := heq.of_subset_closure hlhs hrhs subset_union_left htclosure
  exact hall (by simp [t])

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    {s : ℂ} (hsre : 0 < s.re) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  rcases lt_trichotomy s.im 0 with hsim | hsim | hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg hsre hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
      hsre hsim hsone
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hsre hsim

end
end RiemannGaussian
