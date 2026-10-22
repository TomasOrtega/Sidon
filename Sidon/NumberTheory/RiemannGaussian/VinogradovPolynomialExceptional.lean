/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedExceptional
import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedMoments
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialDifferencing
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems
import Sidon.NumberTheory.RiemannGaussian.VinogradovTypeMaximum

namespace RiemannGaussian.VinogradovPolynomialExceptional
noncomputable section
open Polynomial RiemannGaussian.VinogradovPolynomialSystems RiemannGaussian.VinogradovPolynomialDifferencing
open RiemannGaussian.VinogradovMixedMoments RiemannGaussian.VinogradovTypeMaximum RiemannGaussian.VinogradovMixedExceptional
theorem exists_distinct_reduction {κ : Type*} [Fintype κ]
    {m d T e P s : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      mixedMoment m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u ≤
        mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u ∧
      mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u ≤
        2 * (distinctCount m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u : ℝ) := by
  obtain ⟨e', G, hG, hdom, hdouble⟩ := exists_doubling_dominant hF P s u
  exact ⟨e', G, hG, hdom, mixedMoment_le_twice_distinct hm s _ u hdouble
    (by simpa only [Fintype.card_fin] using hP)⟩

theorem exists_count_reduction {κ : Type*} [Fintype κ]
    {m d T e P s : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      typeCount d P s F u ≤
        2 * distinctCount m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u := by
  obtain ⟨e', G, hG, hdom, hgood⟩ := exists_distinct_reduction hF hm hP u
  refine ⟨e', G, hG, ?_⟩
  have h := hdom.trans hgood
  rw [← typeCount_eq_mixedMoment] at h
  exact_mod_cast h

end
end RiemannGaussian.VinogradovPolynomialExceptional
