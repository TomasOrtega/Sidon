module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaAngularDiscBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLogProfile
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovAngularZeroFree
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovBalancedScale
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovCubicScale
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovSummedCost
public import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovSummedDisc

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovSummedZeroFree
noncomputable section
open Filter RiemannGaussian.ZetaVinogradovCubicScale
open RiemannGaussian.ZetaVinogradovBalancedScale (width level level_atTop width_pos)
open RiemannGaussian.VinogradovSharperBudget (delta delta_pos)
open RiemannGaussian.VinogradovScaleSelection (heightThreshold)
open scoped Topology

def coefficientLimit : ℝ := 3 * Real.pi / 10640

theorem eventually_parameters {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∀ᶠ t : ℝ in atTop, 48 ≤ order t ∧
      (heightThreshold (8 * order t) : ℝ) + 1 ≤ t ∧
      0 < width C t ∧ width C t < delta (order t) / 28 ∧
      ZetaVinogradovSummedCost.cost C t < 1 := by
  have hlim : 10640 * C / (3 * Real.pi) < 1 := by
    apply (div_lt_one (by positivity : 0 < 3 * Real.pi)).mpr
    unfold coefficientLimit at hClim
    linarith
  filter_upwards [ZetaVinogradovCubicScale.eventually_parameters,
    level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    (width_div_delta_tendsto C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 28)),
    (ZetaVinogradovSummedCost.cost_tendsto hC).eventually (gt_mem_nhds hlim)]
    with t ht hl hs hcost
  refine ⟨ht.1, ht.2, width_pos hC hl, ?_, hcost⟩
  have h := (div_lt_iff₀ (delta_pos (order t))).mp hs
  linarith

theorem cost_abs (C t : ℝ) :
    ZetaVinogradovSummedCost.cost C |t| = ZetaVinogradovSummedCost.cost C t := by
  simp [ZetaVinogradovSummedCost.cost, (abs_invariance C t).1,
    (abs_invariance C t).2.2, ZetaVinogradovSummedCost.budget,
    ZetaAngularDiscBudget.budget, ZetaVinogradovSummedDisc.profile,
    ZetaNearOneLogProfile.height, abs_mul]

theorem exists_eventual_right_margin {C : ℝ} (hC : 0 < C)
    (hClim : C < coefficientLimit) : ∃ T : ℝ, 4 ≤ T ∧
      ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| → width C ρ.1.im < 1 - ρ.1.re := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_parameters hC hClim)
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨hn, ht, hw, hs, hcost⟩ := hT |ρ.1.im| ((le_max_left _ _).trans hρ)
  rw [(abs_invariance C ρ.1.im).1] at hn ht hs
  rw [(abs_invariance C ρ.1.im).2.2] at hw hs
  rw [cost_abs] at hcost
  exact ZetaVinogradovSummedCost.margin_of_budget (order ρ.1.im) hn ρ ht hw hs hcost

theorem exists_eventual_strip {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - width C ρ.1.im := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_right_margin hC hClim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := hz ρ hρ
  have hl := hz (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

end
end RiemannGaussian.ZetaVinogradovSummedZeroFree
