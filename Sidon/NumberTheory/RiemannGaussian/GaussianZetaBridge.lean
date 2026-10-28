module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros

public import Mathlib.Analysis.Calculus.Deriv.Star

@[expose] public section

namespace RiemannGaussian

noncomputable section

lemma iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n
        ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => simp [iteratedDeriv_eq_iterate]
  | succ n ih =>
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih, deriv_conj_conj]

lemma riemannZeta_eq_conj_comp_conj :
    riemannZeta = (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) := by
  funext s
  simp [Function.comp_apply]

theorem iteratedDeriv_riemannZeta_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (iteratedDeriv n riemannZeta s) := by
  have hiter := iteratedDeriv_conj_conj riemannZeta n
  rw [← riemannZeta_eq_conj_comp_conj] at hiter
  have h := congrFun hiter (starRingEnd ℂ s)
  simpa [Function.comp_apply] using h

def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

def nontrivialZetaZeroSet : Set ℂ :=
  {s | IsNontrivialZetaZero s}

theorem nontrivialZetaZeroSet_subset_riemannZetaZeros :
    nontrivialZetaZeroSet ⊆ riemannZetaZeros := by
  intro s hs
  exact hs.1

theorem IsCompact.inter_nontrivialZetaZeroSet_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ nontrivialZetaZeroSet).Finite := by
  exact hS.inter_riemannZetaZeros_finite.subset
    (Set.inter_subset_inter_right S
      nontrivialZetaZeroSet_subset_riemannZetaZeros)

abbrev NontrivialZetaZero := {s : ℂ // IsNontrivialZetaZero s}

namespace NontrivialZetaZero

def conjugate (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨starRingEnd ℂ ρ.1, ?_⟩
  refine ⟨by simp [ρ.2.1], ?_, ?_⟩
  · rintro ⟨n, hn⟩
    apply ρ.2.2.1
    refine ⟨n, ?_⟩
    have h := congrArg (starRingEnd ℂ) hn
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    rw [map_mul, map_neg, htwo] at h
    simpa using h
  · intro hone
    apply ρ.2.2.2
    have h := congrArg (starRingEnd ℂ) hone
    simpa using h

@[simp]
theorem conjugate_coe (ρ : NontrivialZetaZero) :
    (conjugate ρ : ℂ) = starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugate_conjugate (ρ : NontrivialZetaZero) :
    conjugate (conjugate ρ) = ρ := by
  apply Subtype.ext
  simp

theorem coe_ne_zero (ρ : NontrivialZetaZero) : (ρ.1 : ℂ) ≠ 0 := by
  intro hzero
  have hzeta := ρ.2.1
  rw [hzero, riemannZeta_zero] at hzeta
  norm_num at hzeta

theorem GammaR_ne_zero (ρ : NontrivialZetaZero) :
    Complex.Gammaℝ ρ.1 ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  cases n with
  | zero =>
      apply coe_ne_zero ρ
      simpa using hn
  | succ n =>
      apply ρ.2.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

theorem completedRiemannZeta_eq_zero (ρ : NontrivialZetaZero) :
    completedRiemannZeta ρ.1 = 0 := by
  have hzeta := ρ.2.1
  rw [riemannZeta_def_of_ne_zero (coe_ne_zero ρ)] at hzeta
  exact (div_eq_zero_iff.mp hzeta).resolve_right (GammaR_ne_zero ρ)

def functionalPartner (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨1 - ρ.1, ?_⟩
  have hcompleted : completedRiemannZeta (1 - ρ.1) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact completedRiemannZeta_eq_zero ρ
  have hzero : riemannZeta (1 - ρ.1) = 0 := by
    rw [riemannZeta_def_of_ne_zero]
    · rw [hcompleted, zero_div]
    · exact sub_ne_zero.mpr ρ.2.2.2.symm
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hRe : 1 ≤ ρ.1.re := by
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hRe ρ.2.1
  · intro hone
    apply coe_ne_zero ρ
    exact sub_eq_self.mp hone

@[simp]
theorem functionalPartner_coe (ρ : NontrivialZetaZero) :
    (functionalPartner ρ : ℂ) = 1 - ρ.1 := rfl

def conjugatePartner (ρ : NontrivialZetaZero) : NontrivialZetaZero :=
  functionalPartner (conjugate ρ)

@[simp]
theorem conjugatePartner_coe (ρ : NontrivialZetaZero) :
    (conjugatePartner ρ : ℂ) = 1 - starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugatePartner_conjugatePartner (ρ : NontrivialZetaZero) :
    conjugatePartner (conjugatePartner ρ) = ρ := by
  apply Subtype.ext
  simp

end NontrivialZetaZero

abbrev ZetaZeroMultiplicity := NontrivialZetaZero → ℕ

noncomputable def analyticZetaZeroMultiplicity : ZetaZeroMultiplicity :=
  fun ρ => analyticOrderNatAt riemannZeta ρ.1

lemma analyticAt_riemannZeta_nontrivialZero (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ riemannZeta ρ.1 := by
  exact analyticOn_riemannZeta ρ.1 (by simpa using ρ.2.2.2)

lemma analyticAt_completedRiemannZeta_nontrivialZero
    (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ completedRiemannZeta ρ.1 := by
  let U : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hUopen : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hρU : ρ.1 ∈ U := by
    exact ⟨by simpa using NontrivialZetaZero.coe_ne_zero ρ,
      by simpa using ρ.2.2.2⟩
  apply DifferentiableOn.analyticAt (s := U) _ (hUopen.mem_nhds hρU)
  intro z hz
  exact (differentiableAt_completedZeta
    (by simpa [U] using hz.1) (by simpa [U] using hz.2)).differentiableWithinAt

theorem analyticOrderAt_riemannZeta_eq_completedRiemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 =
      analyticOrderAt completedRiemannZeta ρ.1 := by
  let inverseGamma : ℂ → ℂ := fun z => (Complex.Gammaℝ z)⁻¹
  have hinverseAnalytic : AnalyticAt ℂ inverseGamma ρ.1 := by
    exact Complex.differentiable_Gammaℝ_inv.analyticAt ρ.1
  have hinverseOrder : analyticOrderAt inverseGamma ρ.1 = 0 := by
    exact hinverseAnalytic.analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (NontrivialZetaZero.GammaR_ne_zero ρ))
  have heq :
      riemannZeta =ᶠ[nhds ρ.1]
        fun z => completedRiemannZeta z * inverseGamma z := by
    filter_upwards [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ)] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta ρ.1 =
        analyticOrderAt
          (fun z => completedRiemannZeta z * inverseGamma z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt completedRiemannZeta ρ.1 +
        analyticOrderAt inverseGamma ρ.1 :=
      analyticOrderAt_mul
        (analyticAt_completedRiemannZeta_nontrivialZero ρ) hinverseAnalytic
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hinverseOrder, add_zero]

theorem analyticOrderAt_riemannZeta_conjugate
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta (NontrivialZetaZero.conjugate ρ).1 =
      analyticOrderAt riemannZeta ρ.1 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero
        (NontrivialZetaZero.conjugate ρ)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero ρ)]
  simp [iteratedDeriv_riemannZeta_conj]

theorem analyticOrderAt_riemannZeta_nontrivialZero_ne_top
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[nhds ρ.1] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpreconnected : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hglobal : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpreconnected
        (by simpa using ρ.2.2.2) hlocal
  have hzetaTwo : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hzetaTwo

def IsPositiveZetaZeroMultiplicity
    (multiplicity : ZetaZeroMultiplicity) : Prop :=
  ∀ ρ, 0 < multiplicity ρ

theorem analyticZetaZeroMultiplicity_positive :
    IsPositiveZetaZeroMultiplicity analyticZetaZeroMultiplicity := by
  intro ρ
  change 0 < analyticOrderNatAt riemannZeta ρ.1
  have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
  have horder : analyticOrderAt riemannZeta ρ.1 ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨analyticAt_riemannZeta_nontrivialZero ρ, ρ.2.1⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  rw [hzero, Nat.cast_zero] at hcast
  exact horder hcast.symm

@[simp]
theorem analyticZetaZeroMultiplicity_conjugate
    (ρ : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugate ρ) =
      analyticZetaZeroMultiplicity ρ := by
  unfold analyticZetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_conjugate]

end

end RiemannGaussian
