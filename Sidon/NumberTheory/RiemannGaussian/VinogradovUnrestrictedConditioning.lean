module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovBinomialRows
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedDifferencing
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialConditionedDescent
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialDifferencing
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialNonsingular
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialPrimeTransfer
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRowTransport
public import Sidon.NumberTheory.RiemannGaussian.VinogradovTypeMaximum

@[expose] public section

namespace RiemannGaussian.VinogradovUnrestrictedConditioning
noncomputable section
open scoped BigOperators
open Polynomial RiemannGaussian.VinogradovPolynomialSystems RiemannGaussian.VinogradovPolynomialDifferencing
open RiemannGaussian.VinogradovTypeMaximum RiemannGaussian.VinogradovPolynomialPrimeTransfer
open RiemannGaussian.VinogradovPolynomialNonsingular RiemannGaussian.VinogradovMixedDifferencing
open RiemannGaussian.VinogradovBinomialRows RiemannGaussian.VinogradovRowTransport
theorem exists_conditioning_of_packet {m d T e P s M U r Q q : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q) :
    ∃ (e' p xi : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' ∧ M < p ∧ p ≤ U ∧ ¬p ∣ T ∧ xi < p ∧
      (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((4 * π.card * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
            residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
              (fullFrequency d G) (monomialTail m d p q (Q / p)) := by
  obtain ⟨e', p, H, hH, hp, hpM, hpU, hpT, hcount⟩ :=
    exists_prime_carrying_count_of_packet hF hm hP hT0 hT π hπ hbudget
      (monomialTail m d 1 q Q)
  let : Fact p.Prime := ⟨hp⟩
  have hfloor : 16 * s ^ 2 ≤ Q / p := (Nat.le_div_iff_mul_le hp.pos).mpr
    ((Nat.mul_le_mul_left (16 * s ^ 2) hpU).trans hQ)
  obtain ⟨xi, hxi, hG, hcondition⟩ :=
    VinogradovPolynomialConditionedDescent.exists_conditioning
      (by omega : d + m < p) (by omega : 2 < p) hpT hr1 hr hds hs hH P Q q hq hfloor
  refine ⟨e', p, xi, hp, rowSystem d (shiftAmount p q xi) H,
    hG, hpM, hpU, hpT, hxi, ?_⟩
  have hc : (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
      ((2 * π.card : ℕ) : ℝ) * (nonsingularCount p m d P s H (monomialTail m d 1 q Q) : ℝ) := by
    exact_mod_cast hcount
  have h := hc.trans (mul_le_mul_of_nonneg_left hcondition (Nat.cast_nonneg (2 * π.card)))
  convert h using 1
  try rfl
  push_cast
  ring

end
end RiemannGaussian.VinogradovUnrestrictedConditioning
