module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovEndpointDeletion
public import Sidon.NumberTheory.RiemannGaussian.VinogradovLowDegreeTail
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedMoments
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentPartition
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialNonsingular
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResidueMoment

@[expose] public section

namespace RiemannGaussian.VinogradovResidueEndpoint
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovPartitionEnergy RiemannGaussian.VinogradovMomentPartition RiemannGaussian.VinogradovLowDegreeTail
open RiemannGaussian.VinogradovPolynomialNonsingular RiemannGaussian.VinogradovResidueMoment RiemannGaussian.VinogradovEndpointDeletion
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def integerTail (m d : ℕ) (x : ℤ) : (Fin d ⊕ Fin m) → ℤ :=
  Sum.elim (fun i => x ^ (i.val + 1)) (fun i => x ^ (d + i.val + 1))

theorem monomialTail_eq_integerTail (m d p q Q : ℕ) (x : Fin Q) :
    monomialTail m d p q Q x =
      integerTail m d (((p * q : ℕ) : ℤ) * ((x.val + 1 : ℕ) : ℤ)) := by
  funext i
  rcases i with i | i <;>
    simp only [monomialTail, integerTail, Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_one]

def shiftedTail (m d p q xi : ℕ) (x : ℕ) : (Fin d ⊕ Fin m) → ℤ :=
  integerTail m d ((q : ℤ) * ((p : ℤ) * x + ((xi : ℤ) - p)))

theorem residue_tail_reconstruction (m d p q xi Q : ℕ) (x : ResidueWindow p xi Q) :
    monomialTail m d 1 q Q x.val =
      shiftedTail m d p q xi ((residueQuotient x).val + 1) := by
  rw [monomialTail_eq_integerTail]
  simp only [shiftedTail, residue_reconstruction, Nat.one_mul]

theorem class_polynomial {p : ℕ} [NeZero p] (m d Q q : ℕ) (c : ZMod p)
    (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (monomialTail m d 1 q Q) (targetWeight tailResidue (fun _ => 1) c) theta =
      polynomial (fun x : ResidueWindow p c.val Q => monomialTail m d 1 q Q x.val)
        (fun _ => 1) theta := by
  have hc (x : Fin Q) : tailResidue (p := p) x = c ↔ (x.val + 1) % p = c.val := by
    constructor
    · intro he
      simpa only [tailResidue, ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective p
      simpa only [tailResidue, ZMod.val_natCast] using he
  unfold polynomial
  simp only [targetWeight, ite_mul, one_mul, zero_mul, hc]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin Q => (x.val + 1) % p = c.val))
    (by simp) (fun x : Fin Q => mFourier (monomialTail m d 1 q Q x) theta)]
  simp only [Finset.sum_filter]

theorem tailClassMoment_eq {p : ℕ} [NeZero p] (m d P Q q s : ℕ)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c =
      VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : ResidueWindow p c.val Q => monomialTail m d 1 q Q x.val) := by
  unfold tailClassMoment VinogradovMixedMoments.mixedMoment
  simp only [mul_one, class_polynomial]

theorem tailClassMoment_le_quotient {p : ℕ} [NeZero p] (m d P Q q s : ℕ)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c ≤
      VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : Fin (Q / p + 1) => shiftedTail m d p q c.val (x.val + 1)) := by
  rw [tailClassMoment_eq]
  have he := mixedMoment_map_le 1 s (windowFrequency (p := p) (P := P) d F)
    (fun x : Fin (Q / p + 1) => shiftedTail m d p q c.val (x.val + 1))
    (residueQuotient (q := p) (xi := c.val) (X := Q)) residueQuotient_injective
  simpa only [residue_tail_reconstruction] using he

theorem tailClassMoment_le_floor {p s : ℕ} [NeZero p]
    (hs : 1 ≤ s) (m d P Q q : ℕ) (hQ : 16 * s ^ 2 ≤ Q / p)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c ≤
      2 * VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : Fin (Q / p) => shiftedTail m d p q c.val (x.val + 1)) :=
  (tailClassMoment_le_quotient m d P Q q s F c).trans
    (mixedMoment_succ_le hs hQ 1 (windowFrequency (p := p) (P := P) d F)
      (shiftedTail m d p q c.val))

theorem exists_floor_tail_bound {p d s : ℕ} [Fact p.Prime]
    (hdp : d < p) (hds : d ≤ s) (hs : 1 ≤ s)
    (m P Q q : ℕ) (hq : 0 < q) (hQ : 16 * s ^ 2 ≤ Q / p) (F : Fin m → ℤ[X]) :
    ∃ xi : ℕ, xi < p ∧
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((2 * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
            (fun x : Fin (Q / p) => shiftedTail m d p q xi (x.val + 1)) := by
  obtain ⟨c, hc⟩ := exists_tail_class_bound hdp hds hs m P Q q hq F
  refine ⟨c.val, ZMod.val_lt c, ?_⟩
  have he := hc.trans (mul_le_mul_of_nonneg_left (tailClassMoment_le_floor hs m d P Q q hQ F c)
    (Nat.cast_nonneg _))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, mul_left_comm] using he

end
end RiemannGaussian.VinogradovResidueEndpoint
