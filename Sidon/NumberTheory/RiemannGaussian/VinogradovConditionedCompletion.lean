module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResidueMoment

@[expose] public section

namespace RiemannGaussian.VinogradovConditionedCompletion
noncomputable section
open scoped BigOperators Classical

abbrev PrimeTailWindow (p b : ℕ) (eta : ℤ) (X : ℕ) :=
  VinogradovResidueMoment.ResidueWindow (p ^ b) (eta : ZMod (p ^ b)).val X

end
end RiemannGaussian.VinogradovConditionedCompletion
