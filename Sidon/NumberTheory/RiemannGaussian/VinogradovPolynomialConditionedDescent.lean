/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovBinomialRows
import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedDifferencing
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialDifferencing
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialNonsingular
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems
import Sidon.NumberTheory.RiemannGaussian.VinogradovResidueEndpoint
import Sidon.NumberTheory.RiemannGaussian.VinogradovRowTransport

namespace RiemannGaussian.VinogradovPolynomialConditionedDescent
noncomputable section
open scoped BigOperators Classical
open Polynomial RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovPolynomialSystems
open RiemannGaussian.VinogradovPolynomialDifferencing RiemannGaussian.VinogradovPolynomialNonsingular
open RiemannGaussian.VinogradovMixedDifferencing RiemannGaussian.VinogradovMixedMoments
open RiemannGaussian.VinogradovBinomialRows RiemannGaussian.VinogradovResidueEndpoint RiemannGaussian.VinogradovRowTransport
theorem exists_conditioning {p m d r T e s : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (P Q q : ℕ) (hq : 0 < q) (hQ : 16 * s ^ 2 ≤ Q / p) :
    ∃ xi : ℕ, xi < p ∧ HasType (rowSystem d (shiftAmount p q xi) F) d T e ∧
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((2 * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
            residueMixedMoment m s P (p ^ r) (pow_pos (Fact.out : p.Prime).pos r)
              (fullFrequency d (rowSystem d (shiftAmount p q xi) F))
              (monomialTail m d p q (Q / p)) := by
  obtain ⟨xi, hxi, hbound⟩ := exists_floor_tail_bound (by omega : d < p) hds hs m P Q q hq hQ F
  have hG := hasType_rowSystem hF (shiftAmount p q xi)
  refine ⟨xi, hxi, hG, ?_⟩
  rw [shifted_mixedMoment_eq_count] at hbound
  have hc := prime_dilated_count_le hpdeg hp2 hpT hr1 hr hG P (Q / p) q s
  have he := hbound.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
  simpa only [mul_assoc] using he

end
end RiemannGaussian.VinogradovPolynomialConditionedDescent
