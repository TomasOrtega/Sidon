module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedDifferencing
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMixedMoments
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNonsingularDescent
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPartitionEnergy
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialDifferencing
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialNonsingular
public import Sidon.NumberTheory.RiemannGaussian.VinogradovPolynomialSystems
public import Sidon.NumberTheory.RiemannGaussian.VinogradovTypeMaximum
public import Sidon.NumberTheory.RiemannGaussian.VinogradovUnrestrictedConditioning

@[expose] public section

namespace RiemannGaussian.VinogradovDiagonalMoment
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovPartitionEnergy
open RiemannGaussian.VinogradovPolynomialSystems RiemannGaussian.VinogradovPolynomialDifferencing
open RiemannGaussian.VinogradovTypeMaximum RiemannGaussian.VinogradovPolynomialNonsingular
open RiemannGaussian.VinogradovMixedMoments RiemannGaussian.VinogradovMixedDifferencing RiemannGaussian.VinogradovNonsingularDescent
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def monomialSystem (k : ℕ) (j : Fin k) : ℤ[X] := X ^ (j.val + 1)

theorem monomialSystem_hasType (k : ℕ) : HasType (monomialSystem k) 0 1 0 := by
  intro j
  simp [monomialSystem]

theorem mixedMoment_self {ι a : Type*} [Fintype ι] [Fintype a]
    (m s : ℕ) (v : ι → a → ℤ) : mixedMoment m s v v = moment (m + s) v := by
  unfold mixedMoment moment
  simp only [polynomial, one_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← pow_add]
  congr 1
  omega

theorem initial_frequency (k P : ℕ) :
    (fun x : Fin P => fullFrequency 0 (monomialSystem k) (x.val + 1)) =
      monomialTail k 0 1 1 P := by
  funext x j
  rcases j with j | j
  · exact Fin.elim0 j
  · simp [fullFrequency, monomialSystem, monomialTail]

theorem initial_count_eq (k s P : ℕ) :
    (typeCount 0 P s (monomialSystem k) (monomialTail k 0 1 1 P) : ℝ) =
      meanValue (s + k) k P := by
  rw [typeCount_eq_mixedMoment, initial_frequency, mixedMoment_self,
    monomialTail_moment _ _ _ _ _ _ (by norm_num) (by norm_num)]
  simp only [Nat.zero_add, Nat.add_comm k s]

theorem exists_diagonal_moment_step_of_packet {k s P M U : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M)
    (π : Finset ℕ) (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (2 * k.choose 2) < ∏ p ∈ π, p)
    (hroot : P < (M + 1) ^ k) (hs : 1 ≤ s)
    (hQ : 16 * s ^ 2 * U ≤ P) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ U ∧
      meanValue (s + k) k P ≤
        ((4 * π.card * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ (2 * s + k * (k - 1) / 2) * (P : ℝ) ^ k *
            meanValue s k (P / p) := by
  obtain ⟨e', p, xi, hp, G, hG, hpM, hpU, hpT, hxi, hcount⟩ :=
    VinogradovUnrestrictedConditioning.exists_conditioning_of_packet (monomialSystem_hasType k)
      hk hP (by simpa only [Nat.zero_add] using hM) (by norm_num) (by simp) π hπ
      (by simpa only [Nat.zero_add] using hbudget) (by omega : 1 ≤ k)
      (by omega : k ≤ 0 + k) (by omega : 0 ≤ s) hs (by norm_num : 0 < 1) hQ
  have hpk : P < p ^ k :=
    hroot.trans_le (Nat.pow_le_pow_left (by omega : M + 1 ≤ p) k)
  rw [initial_count_eq,
    residueMixedMoment_eq_diagonal k s P (p ^ k) (pow_pos hp.pos k) hpk,
    monomialTail_moment _ _ _ _ _ _ hp.pos (by norm_num)] at hcount
  refine ⟨p, hp, hpM, hpU, ?_⟩
  convert hcount using 1
  simp only [Nat.zero_add, Nat.sub_zero, Nat.factorial_zero, mul_one,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

end
end RiemannGaussian.VinogradovDiagonalMoment
