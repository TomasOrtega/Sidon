module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Bertrand
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCrossMoment

@[expose] public section

namespace RiemannGaussian.VinogradovFirstExponent
noncomputable section
open scoped Classical BigOperators
open RiemannGaussian.VinogradovMeanValue
theorem crossCount_le_of_embedding {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (w : κ → d → ℤ) (e : ι ↪ κ) (he : ∀ i, w (e i) = v i) :
    VinogradovCrossMoment.crossCount v v ≤ VinogradovCrossMoment.crossCount w w := by
  unfold VinogradovCrossMoment.crossCount
  apply Finset.card_le_card_of_injOn (fun xy => (e xy.1, e xy.2))
  · intro xy hxy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [he]
    exact (Finset.mem_filter.mp hxy).2
  · intro xy _ zw _ h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))

end
end RiemannGaussian.VinogradovFirstExponent
