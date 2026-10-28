module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCoarseCongruence
public import Sidon.NumberTheory.RiemannGaussian.VinogradovConditionedCompletion
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentPartition
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSignedCongruence

@[expose] public section

namespace RiemannGaussian.VinogradovResidueEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMomentPartition
abbrev GoodResidue (p k a b xi : ℕ) :=
  {x : Fin k → Fin (p ^ (k * b)) //
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p))}

def residueTuple {p k b : ℕ} [NeZero p] (x : Fin k → ℕ) : Fin k → Fin (p ^ (k * b)) :=
  fun j => ⟨x j % p ^ (k * b), Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

def residueSignature {p k a b xi : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (x : GoodResidue p k a b xi) : (i : Fin k) → ZMod (p ^ ((i.val + 1) * b)) :=
  blockSignature (q := p) (b := b) eta (fun j => VinogradovSignedCongruence.sign (colour j))
    (fun _ : Unit => fun j => ((x.val j).val : ℤ)) ()

theorem residueSignature_card_le {p k a b xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a ≤ b) (eta : ℤ) (colour : Fin k → Bool)
    (target : (i : Fin k) → ZMod (p ^ ((i.val + 1) * b))) :
    (Finset.univ.filter (fun x : GoodResidue p k a b xi =>
      residueSignature eta colour x = target)).card ≤
      p ^ ((a + b) * (k * (k - 1) / 2)) * VinogradovSignedCongruence.colourFactorial colour := by
  apply le_trans (Finset.card_le_card_of_injOn Subtype.val ?_ ?_)
    (VinogradovCoarseCongruence.conditioned_residue_card_le hkp hk hab colour xi eta
      (fun i => ((target i).val : ℤ)))
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property.1, x.property.2, ?_⟩
    intro i
    have he := congrFun (Finset.mem_filter.mp hx).2 i
    have hc : ((∑ j, VinogradovSignedCongruence.sign (colour j) *
        (((x.val j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) : ZMod (p ^ ((i.val + 1) * b))) =
        (((target i).val : ℤ) : ZMod (p ^ ((i.val + 1) * b))) := by
      simpa only [residueSignature, blockSignature, Int.cast_natCast, ZMod.natCast_zmod_val] using he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ ((i.val + 1) * b))).mp hc.symm
    simpa only [Nat.cast_pow] using hd
  · exact fun _ _ _ _ h => Subtype.val_injective h

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev ConditionedWindow (p k a xi X : ℕ) :=
  {x : Fin k → Fin X //
    (∀ j, ((x j).val + 1) % p ^ a = xi) ∧
    Function.Injective (fun j => ((((x j).val + 1) / p ^ a : ℕ) : ZMod p))}

abbrev WindowConfiguration (p k a b r xi X : ℕ) (eta : ℤ) :=
  ConditionedWindow p k a xi X ×
    (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X)

def windowBlock {p k a b r xi X : ℕ} {eta : ℤ}
    (z : WindowConfiguration p k a b r xi X eta) : Fin k → ℕ :=
  fun j => (z.1.val j).val + 1

def windowFrequency {p k a b r xi X : ℕ} {eta : ℤ}
    (colour : Fin k → Bool) (tau : Fin r → ℤ) :
    WindowConfiguration p k a b r xi X eta → Fin k → ℤ :=
  mixedFrequency (fun j => VinogradovSignedCongruence.sign (colour j)) tau
    (fun z j => (windowBlock z j : ℤ)) (fun z j => ((z.2 j).val.val + 1 : ℤ))

end
end RiemannGaussian.VinogradovResidueEnergy
