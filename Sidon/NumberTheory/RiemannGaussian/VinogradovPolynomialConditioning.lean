/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovMomentPartition
import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialDifferencing
import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems
import Sidon.NumberTheory.RiemannGaussian.VinogradovProductEnergy
import Sidon.NumberTheory.RiemannGaussian.VinogradovResidueEnergy

namespace RiemannGaussian.VinogradovPolynomialConditioning
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment
open RiemannGaussian.VinogradovMomentPartition RiemannGaussian.VinogradovPartitionEnergy RiemannGaussian.VinogradovPolynomialSystems
open RiemannGaussian.VinogradovPolynomialDifferencing
abbrev GoodResidue (p m r : ℕ) :=
  {c : Fin m → Fin (p ^ r) // Function.Injective (fun j => ((c j).val : ZMod p))}

def signature {m : ℕ} (p d r : ℕ) (F : Fin m → ℤ[X]) (x : Fin m → ℕ) :
    (i : Fin m) → ZMod (p ^ min (d + i.val + 1) r) :=
  fun i => ((∑ j, (F i).eval (x j : ℤ) : ℤ) : ZMod (p ^ min (d + i.val + 1) r))

def residueSignature {p m r : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (c : GoodResidue p m r) :
    (i : Fin m) → ZMod (p ^ min (d + i.val + 1) r) :=
  signature p d r F (fun j => (c.val j).val)

theorem residueSignature_card_le {p m d r T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (a : (i : Fin m) → ZMod (p ^ min (d + i.val + 1) r)) :
    (Finset.univ.filter (fun c : GoodResidue p m r => residueSignature d F c = a)).card ≤
      p ^ ((r - d) * (r - d - 1) / 2) * m.factorial := by
  apply le_trans (Finset.card_le_card_of_injOn Subtype.val ?_ ?_)
    (type_integer_congruence_card_le hpdeg hp2 hpT hr hF (fun i => ((a i).val : ℤ)))
  · intro c hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c.property, ?_⟩
    intro i
    have he := congrFun (Finset.mem_filter.mp hc).2 i
    have hz : ((∑ j, (F i).eval ((c.val j).val : ℤ) : ℤ) :
        ZMod (p ^ min (d + i.val + 1) r)) =
      (((a i).val : ℤ) : ZMod (p ^ min (d + i.val + 1) r)) := by
      simpa only [residueSignature, signature, Int.cast_natCast, ZMod.natCast_zmod_val] using he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ min (d + i.val + 1) r)).mp hz.symm
    simpa only [Nat.cast_pow] using hd
  · exact fun _ _ _ _ he => Subtype.val_injective he

theorem cast_mod_power {p r b : ℕ} (hbr : b ≤ r) (n : ℕ) :
    ((n % p ^ r : ℕ) : ZMod (p ^ b)) = (n : ZMod (p ^ b)) :=
  (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    (Nat.mod_mod_of_dvd n (pow_dvd_pow p hbr))

theorem cast_mod_power_prime {p r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    ((n % p ^ r : ℕ) : ZMod p) = (n : ZMod p) := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  apply Nat.mod_mod_of_dvd
  simpa only [pow_one] using pow_dvd_pow p hr

def residueTuple {p : ℕ} (hp : 0 < p) (m r : ℕ) (x : Fin m → ℕ) : Fin m → Fin (p ^ r) :=
  fun j => ⟨x j % p ^ r, Nat.mod_lt _ (pow_pos hp r)⟩

def goodResidue {p m r : ℕ} (hp : 0 < p) (hr : 1 ≤ r) (x : Fin m → ℕ)
    (hx : Function.Injective (fun j => (x j : ZMod p))) : GoodResidue p m r := by
  refine ⟨residueTuple hp m r x, ?_⟩
  intro i j he
  apply hx
  simpa only [residueTuple, cast_mod_power_prime hr] using he

theorem signature_residueTuple {p m r : ℕ} (hp : 0 < p)
    (d : ℕ) (F : Fin m → ℤ[X]) (x : Fin m → ℕ) :
    signature p d r F (fun j => (residueTuple hp m r x j).val) = signature p d r F x := by
  funext i
  simp only [signature, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let f := Int.castRingHom (ZMod (p ^ min (d + i.val + 1) r))
  have heval (n : ℕ) :
      (((F i).eval (n : ℤ) : ℤ) : ZMod (p ^ min (d + i.val + 1) r)) =
        ((F i).map f).eval (n : ZMod (p ^ min (d + i.val + 1) r)) := by
    simpa only [f, Int.coe_castRingHom, Int.cast_natCast] using
      (Polynomial.eval_map_apply (p := F i) f (n : ℤ)).symm
  simp only [residueTuple, heval, cast_mod_power (Nat.min_le_right _ _)]

def blockFrequency {m : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (x : Fin m → ℕ) :
    (Fin d ⊕ Fin m) → ℤ := ∑ j, fullFrequency d F (x j)

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem configuration_integral_le {ι : Type*} [Fintype ι]
    {p m d r T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr1 : 1 ≤ r) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (x : ι → Fin m → ℕ) (tail : ι → (Fin d ⊕ Fin m) → ℤ) (w : ι → ℂ)
    (hx : ∀ z, Function.Injective (fun j => (x z j : ZMod p)))
    (htail : ∀ z i, (p : ℤ) ^ min (d + i.val + 1) r ∣ tail z (Sum.inr i)) :
    (∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
      ‖polynomial (fun z => blockFrequency d F (x z) + tail z) w theta‖ ^ 2) ≤
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
        ∑ c : GoodResidue p m r, ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
          ‖polynomial (fun z => blockFrequency d F (x z) + tail z)
            (targetWeight (fun z => residueTuple (Fact.out : p.Prime).pos m r (x z)) w c.val) theta‖ ^ 2 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let fine (z : ι) := goodResidue hp hr1 (x z) (hx z)
  let v (z : ι) := blockFrequency d F (x z) + tail z
  have hs (z : ι) : residueSignature d F (fine z) = signature p d r F (x z) :=
    signature_residueTuple hp d F (x z)
  have hz (z : ι) (i : Fin m) :
      (tail z (Sum.inr i) : ZMod (p ^ min (d + i.val + 1) r)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa only [Nat.cast_pow] using htail z i
  have hcollision (z z' : ι) (he : v z = v z') :
      residueSignature d F (fine z) = residueSignature d F (fine z') := by
    rw [hs, hs]
    funext i
    have hi := congrArg (fun n : ℤ => (n : ZMod (p ^ min (d + i.val + 1) r)))
      (congrFun he (Sum.inr i))
    simpa only [v, blockFrequency, fullFrequency, Pi.add_apply, Finset.sum_apply,
      Sum.elim_inr, Int.cast_add, hz, add_zero, signature] using hi
  have hc (a : (i : Fin m) → ZMod (p ^ min (d + i.val + 1) r)) :
      ((Finset.univ.filter (fun c : GoodResidue p m r => residueSignature d F c = a)).card : ℝ) ≤
        ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) := by
    exact_mod_cast residueSignature_card_le hpdeg hp2 hpT hr hF a
  have he := whole_integral_le v w fine (residueSignature d F)
    ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) hcollision (by
      intro a
      convert hc a using 1
      congr 2
      ext c
      simp)
  have hw (c : GoodResidue p m r) : targetWeight fine w c =
      targetWeight (fun z => residueTuple hp m r (x z)) w c.val := by
    funext z
    unfold targetWeight
    have hiff : fine z = c ↔ residueTuple hp m r (x z) = c.val := by
      constructor
      · exact congrArg Subtype.val
      · intro he
        apply Subtype.ext
        exact he
    rw [hiff]
  simpa only [v, hw] using he

end
end RiemannGaussian.VinogradovPolynomialConditioning
