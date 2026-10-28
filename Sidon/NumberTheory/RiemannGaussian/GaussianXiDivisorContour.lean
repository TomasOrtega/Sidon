module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Sidon.NumberTheory.RiemannGaussian.GaussianSpectral
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
public import Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry

@[expose] public section

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hder := congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  rw [deriv_comp_const_sub] at hder
  simpa using congrArg Neg.neg hder

theorem spectralZetaZeroWindowSet_finite
    {T : ℝ} (_hT : 0 ≤ T) :
    {ρ : NontrivialZetaZero |
      |(zetaSpectralCoordinate ρ.1).re| ≤ T}.Finite := by
  let B : Set ℂ :=
    Metric.closedBall (0 : ℂ) (T + 1) ∩ nontrivialZetaZeroSet
  have hB : B.Finite := by
    exact IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) (T + 1))
  have hpre :
      ((fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⁻¹' B).Finite :=
    hB.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  change (ρ.1 : ℂ) ∈ B
  refine ⟨?_, ρ.2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm := Complex.norm_le_abs_re_add_abs_im ρ.1
  have hre : |ρ.1.re| < 1 := by
    rw [abs_of_pos (NontrivialZetaZero.zero_lt_re ρ)]
    exact NontrivialZetaZero.re_lt_one ρ
  have him : |ρ.1.im| ≤ T := by
    change |(zetaSpectralCoordinate ρ.1).re| ≤ T at hρ
    simpa only [zetaSpectralCoordinate_re] using hρ
  linarith

noncomputable def spectralZetaZeroWindow
    (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindowSet_finite
    (T := max T 0) (le_max_right T 0)).toFinset

@[simp]
theorem mem_spectralZetaZeroWindow
    {T : ℝ} (hT : 0 ≤ T) (ρ : NontrivialZetaZero) :
    ρ ∈ spectralZetaZeroWindow T ↔
      |(zetaSpectralCoordinate ρ.1).re| ≤ T := by
  unfold spectralZetaZeroWindow
  rw [Set.Finite.mem_toFinset]
  change |(zetaSpectralCoordinate ρ.1).re| ≤ max T 0 ↔ _
  rw [max_eq_left hT]

end

end RiemannGaussian
