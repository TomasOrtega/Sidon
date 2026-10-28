module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

namespace RiemannGaussian

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
def riemannThetaTail (x : ℝ) : ℂ :=
  (HurwitzZeta.evenKernel 0 x : ℂ) - 1

theorem continuousOn_riemannThetaTail :
    ContinuousOn riemannThetaTail (Ioi 0) := by
  unfold riemannThetaTail
  exact (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel 0)).sub continuousOn_const

theorem exists_riemannThetaTail_exp_bound :
    ∃ (C p : ℝ), 1 ≤ C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x) := by
  obtain ⟨p, hp, hbigO⟩ :=
    HurwitzZeta.isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  have hbigO' :
      riemannThetaTail =O[atTop] fun x : ℝ => Real.exp (-p * x) := by
    change (fun x : ℝ =>
      (HurwitzZeta.evenKernel 0 x : ℂ) - 1) =O[atTop]
        fun x : ℝ => Real.exp (-p * x)
    simpa using Complex.isBigO_ofReal_left.mpr hbigO
  obtain ⟨Ctop, hCtop⟩ := hbigO'.bound
  rw [eventually_atTop] at hCtop
  obtain ⟨a, ha⟩ := hCtop
  let M : ℝ := max 1 a
  have hM1 : 1 ≤ M := le_max_left _ _
  have haM : a ≤ M := le_max_right _ _
  have hcontinuous : ContinuousOn (fun x => ‖riemannThetaTail x‖)
      (Icc 1 M) := by
    exact (continuousOn_riemannThetaTail.mono
      (fun x hx => by exact hx.1.trans_lt' zero_lt_one)).norm
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.bddAbove_image hcontinuous)
  let C : ℝ := max 1 (max Ctop (C₀ * Real.exp (p * M)))
  refine ⟨C, p, le_max_left _ _, hp, ?_⟩
  intro x hx
  by_cases hMx : M ≤ x
  · have hbound := ha x (haM.trans hMx)
    have hbound' :
        ‖riemannThetaTail x‖ ≤ Ctop * Real.exp (-p * x) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        using hbound
    have hCtopC : Ctop ≤ C :=
      (le_max_left Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hbound'.trans
      (mul_le_mul_of_nonneg_right hCtopC (Real.exp_nonneg _))
  · have hxM : x ≤ M := le_of_not_ge hMx
    have hnormC₀ : ‖riemannThetaTail x‖ ≤ C₀ := by
      apply hC₀
      exact ⟨x, ⟨hx, hxM⟩, rfl⟩
    have hC₀nonneg : 0 ≤ C₀ :=
      (norm_nonneg (riemannThetaTail x)).trans hnormC₀
    have hratio :
        C₀ ≤ (C₀ * Real.exp (p * M)) * Real.exp (-p * x) := by
      rw [mul_assoc, ← Real.exp_add]
      have hexp : 1 ≤ Real.exp (p * M + -p * x) := by
        rw [Real.one_le_exp_iff]
        nlinarith
      simpa using mul_le_mul_of_nonneg_left hexp hC₀nonneg
    have hcompactC : C₀ * Real.exp (p * M) ≤ C :=
      (le_max_right Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hnormC₀.trans <| hratio.trans <|
      mul_le_mul_of_nonneg_right hcompactC (Real.exp_nonneg _)

def riemannThetaUpper : ℝ → ℂ :=
  (Ioi 1).indicator riemannThetaTail

theorem riemannThetaUpper_eq_tail {x : ℝ} (hx : 1 < x) :
    riemannThetaUpper x = riemannThetaTail x := by
  simp [riemannThetaUpper, hx]

theorem riemannThetaUpper_eq_zero {x : ℝ} (hx : x ≤ 1) :
    riemannThetaUpper x = 0 := by
  simp [riemannThetaUpper, hx]

theorem riemann_f_modif_eq_upper_add_reflection (x : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      riemannThetaUpper x +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x) := by
  by_cases hx : 0 < x
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hinv : 1 < 1 / x := by
        exact (one_lt_div hx).mpr hx1
      rw [riemannThetaUpper_eq_zero hx1.le,
        riemannThetaUpper_eq_tail hinv, zero_add]
      rw [WeakFEPair.f_modif, Pi.add_apply,
        Set.indicator_of_notMem (notMem_Ioi.mpr hx1.le), zero_add,
        Set.indicator_of_mem (mem_Ioo.mpr ⟨hx, hx1⟩)]
      simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply,
        ite_eq_left, one_mul]
      rw [HurwitzZeta.evenKernel_functional_equation]
      push_cast
      rw [Complex.ofReal_cpow hx.le, Complex.ofReal_div,
        Complex.ofReal_one]
      field_simp [hx.ne']
      rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      unfold riemannThetaTail
      simp only [smul_eq_mul, mul_one]
      have hreal :
          x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hx]
        norm_num
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        norm_num
      have hcomplex :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
        rw [hhalf, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul,
          hreal, Complex.ofReal_one]
      have hcpow :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              (x : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _
          (Complex.ofReal_ne_zero.mpr hx.ne')]
        norm_num
      change (HurwitzZeta.evenKernel 0 (1 / x) : ℂ) -
          (x : ℂ) ^ (1 / 2 : ℂ) *
            ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (x : ℂ) ^ (1 / 2 : ℂ) *
          ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((HurwitzZeta.evenKernel 0 (1 / x) : ℂ) - 1))
      rw [hcomplex, ← mul_assoc, hcpow, one_mul]
    · simp [WeakFEPair.f_modif, riemannThetaUpper]
    · have hinv : 1 / x ≤ 1 := by
        exact (div_le_one hx).mpr hx1.le
      rw [riemannThetaUpper_eq_tail hx1,
        riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
      simp [WeakFEPair.f_modif, hx1,
        notMem_Ioo_of_ge hx1.le, riemannThetaTail,
        HurwitzZeta.hurwitzEvenFEPair]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hinv : 1 / x ≤ 1 := by
      by_cases hxzero : x = 0
      · simp [hxzero]
      · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
        exact (div_nonpos_of_nonneg_of_nonpos zero_le_one hxle).trans
          zero_le_one
    rw [riemannThetaUpper_eq_zero (hxle.trans zero_le_one),
      riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
    rw [WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_of_notMem
        (notMem_Ioi.mpr (hxle.trans zero_le_one)),
      Set.indicator_of_notMem (notMem_Ioo_of_le hxle)]
    simp

theorem locallyIntegrableOn_riemannThetaUpper :
    LocallyIntegrableOn riemannThetaUpper (Ioi 0) := by
  have htail : LocallyIntegrableOn riemannThetaTail (Ioi 0) :=
    continuousOn_riemannThetaTail.locallyIntegrableOn measurableSet_Ioi
  intro x hx
  obtain ⟨U, hU, hInt⟩ := htail x hx
  refine ⟨U, hU, ?_⟩
  simpa [riemannThetaUpper] using hInt.indicator measurableSet_Ioi

theorem exists_isBigO_riemannThetaUpper_exp :
    ∃ p : ℝ, 0 < p ∧
      riemannThetaUpper =O[atTop]
        fun x : ℝ => Real.exp (-p * x) := by
  obtain ⟨C, p, hC, hp, hbound⟩ :=
    exists_riemannThetaTail_exp_bound
  refine ⟨p, hp, IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [riemannThetaUpper_eq_tail hx]
  have h := hbound x hx.le
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h

theorem isBigO_riemannThetaUpper_nhdsGT_zero (b : ℝ) :
    riemannThetaUpper =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_le_nhds zero_lt_one).filter_mono
    nhdsWithin_le_nhds] with x hx
  rw [riemannThetaUpper_eq_zero hx]
  simp

theorem mellinConvergent_riemannThetaUpper (s : ℂ) :
    MellinConvergent riemannThetaUpper s := by
  obtain ⟨p, hp, htop⟩ := exists_isBigO_riemannThetaUpper_exp
  apply mellinConvergent_of_isBigO_rpow_exp hp
    locallyIntegrableOn_riemannThetaUpper htop
    (isBigO_riemannThetaUpper_nhdsGT_zero (s.re - 1))
  linarith

def riemannThetaReflection (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x)

theorem riemann_f_modif_eq_upper_add_reflection_fun :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif =
      riemannThetaUpper + riemannThetaReflection := by
  funext x
  exact riemann_f_modif_eq_upper_add_reflection x

theorem mellinConvergent_riemannThetaReflection (s : ℂ) :
    MellinConvergent riemannThetaReflection s := by
  let P := HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)
  have hfmodif : MellinConvergent P.f_modif s := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hupper := mellinConvergent_riemannThetaUpper s
  have hdifference :
      MellinConvergent (fun x => P.f_modif x - riemannThetaUpper x) s :=
    (hasMellin_sub hfmodif hupper).1
  have hreflection :
      riemannThetaReflection =
        fun x => P.f_modif x - riemannThetaUpper x := by
    funext x
    have hdecomp := riemann_f_modif_eq_upper_add_reflection x
    dsimp [P] at hdecomp ⊢
    rw [hdecomp]
    abel
  rw [hreflection]
  exact hdifference

theorem mellin_riemannThetaReflection (s : ℂ) :
    mellin riemannThetaReflection s =
      mellin riemannThetaUpper (1 / 2 - s) := by
  unfold riemannThetaReflection
  calc
    mellin
        (fun x : ℝ =>
          (x : ℂ) ^ (-(1 / 2 : ℂ)) •
            riemannThetaUpper (1 / x)) s =
        mellin (fun x : ℝ => riemannThetaUpper (1 / x))
          (s + -(1 / 2 : ℂ)) :=
      mellin_cpow_smul
        (fun x : ℝ => riemannThetaUpper (1 / x)) s
          (-(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (-(s + -(1 / 2 : ℂ))) := by
      simpa [one_div] using
        mellin_comp_inv riemannThetaUpper (s + -(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (1 / 2 - s) := by
      congr 2
      ring

theorem mellin_riemann_f_modif_eq_upper_add_reflected (s : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s =
      mellin riemannThetaUpper s +
        mellin riemannThetaUpper (1 / 2 - s) := by
  rw [riemann_f_modif_eq_upper_add_reflection_fun]
  change mellin
      (fun x => riemannThetaUpper x + riemannThetaReflection x) s = _
  rw [(hasMellin_add
    (mellinConvergent_riemannThetaUpper s)
    (mellinConvergent_riemannThetaReflection s)).2]
  rw [mellin_riemannThetaReflection]

theorem completedRiemannZeta₀_eq_upperMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)) / 2 := by
  change mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2 = _
  rw [mellin_riemann_f_modif_eq_upper_add_reflected]
  congr 2
  ring_nf

end

end RiemannGaussian
