/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Topology.Algebra.Module.Cardinality
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge

namespace RiemannGaussian

noncomputable section

open Filter Topology
theorem nontrivialZetaZeroSet_countable :
    nontrivialZetaZeroSet.Countable := by
  exact (HereditarilyLindelofSpace.isLindelof
    nontrivialZetaZeroSet).countable_of_isDiscrete
      (isDiscrete_riemannZetaZeros.mono
        nontrivialZetaZeroSet_subset_riemannZetaZeros)

noncomputable instance : Countable NontrivialZetaZero :=
  nontrivialZetaZeroSet_countable.to_subtype

namespace NontrivialZetaZero

theorem re_lt_one (ρ : NontrivialZetaZero) : ρ.1.re < 1 := by
  exact lt_of_not_ge fun h =>
    riemannZeta_ne_zero_of_one_le_re h ρ.2.1

theorem zero_lt_re (ρ : NontrivialZetaZero) : 0 < ρ.1.re := by
  have hpartner := re_lt_one (functionalPartner ρ)
  simpa using hpartner

end NontrivialZetaZero

def SameZetaConjugatePacket
    (ρ σ : NontrivialZetaZero) : Prop :=
  σ = ρ ∨ σ = NontrivialZetaZero.conjugatePartner ρ

@[refl]
theorem SameZetaConjugatePacket.refl (ρ : NontrivialZetaZero) :
    SameZetaConjugatePacket ρ ρ :=
  Or.inl rfl

theorem SameZetaConjugatePacket.symm
    {ρ σ : NontrivialZetaZero}
    (h : SameZetaConjugatePacket ρ σ) :
    SameZetaConjugatePacket σ ρ := by
  rcases h with rfl | rfl
  · exact .refl _
  · exact Or.inr (NontrivialZetaZero.conjugatePartner_conjugatePartner ρ).symm

namespace NontrivialZetaZero

end NontrivialZetaZero

end

end RiemannGaussian
