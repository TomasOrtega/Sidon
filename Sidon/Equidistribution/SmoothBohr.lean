import Sidon.Equidistribution.NormalizedDiscrepancy
import Sidon.Equidistribution.RegularBohr
import Mathlib.Algebra.Order.BigOperators.Expect

/-! # Smooth and regular Bohr equidistribution for extremal Sidon sets -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem sidon_smooth_equidistribution {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card)
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (K : ℝ) (hK : 1 ≤ K)
    (hF : LipschitzWith (Real.toNNReal K) F) (hF0 : ∀ β, 0 ≤ F β) (hF1 : ∀ β, F β ≤ 1)
    (α : Fin d → AddCircle (1 : ℝ)) :
    |(𝔼 x ∈ S, F (x • α)) - (𝔼 x ∈ interval N, F (x • α))| ≤
      48000 * K ^ (2 / 3 : ℝ) *
        (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ^ (1 / (8 * (d : ℝ))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  have hmnat : 0 < S.card := by exact_mod_cast hmpos
  have hI : (interval N).Nonempty := by
    refine ⟨1, mem_interval.mpr ⟨le_rfl, ?_⟩⟩
    exact_mod_cast hN
  have havg (T : Finset ℤ) (hT : T.Nonempty) :
      0 ≤ (𝔼 x ∈ T, F (x • α)) ∧ (𝔼 x ∈ T, F (x • α)) ≤ 1 :=
    ⟨Finset.expect_nonneg (fun x _ => hF0 _), Finset.expect_le hT (fun x _ => hF1 _)⟩
  have hX : |(𝔼 x ∈ S, F (x • α)) - (𝔼 x ∈ interval N, F (x • α))| ≤ 1 := by
    obtain ⟨hS0, hS1⟩ := havg S (Finset.card_pos.mp hmnat)
    obtain ⟨hI0, hI1⟩ := havg (interval N) hI
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hE : 0 < sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)) :=
    add_pos_of_nonneg_of_pos (abs_nonneg _ ) (Real.rpow_pos_of_pos hNpos _)
  apply compact_smoothing_paper_bound hd hX hK hE
  intro η hη hηhalf
  have htest := norm_torusTest_le_compact_smoothing (normalizedDiscrepancy N S) F
    (Real.toNNReal K) hF hF0 hF1 α
    (1600 * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)))) η
    (sidon_normalized_fourier_uniformity_apply hN hS hSN hm) hη hηhalf
  rw [torusTest_normalizedDiscrepancy_complexify, Complex.norm_real, Real.norm_eq_abs,
    Real.coe_toNNReal K (by linarith)] at htest
  have hmass := sum_norm_normalizedDiscrepancy_le_two hN hmnat hSN
  have hmult := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ K * η)
  nlinarith only [htest, hmult]

theorem sidon_regular_bohr_equidistribution {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (α : Fin d → AddCircle (1 : ℝ))
    {ρ : ℝ} (hρ : 0 < ρ) (hreg : IsRegularBohrSet N α ρ) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤
      48100 * ((d : ℝ) / ρ) *
        (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ^ (1 / (14 * (d : ℝ))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmpos : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  have hmnat : 0 < S.card := by exact_mod_cast hmpos
  have hE : 0 < sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)) :=
    add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.rpow_pos_of_pos hNpos _)
  have hbound := regular_bohr_equidistribution_of_smooth hd hN S hSN
    (Finset.card_pos.mp hmnat) α hρ hreg hE (by norm_num : (1 : ℝ) ≤ 48000) (by
      intro K hK F hF0 hF1 hF
      let Fc : C(Fin d → AddCircle (1 : ℝ), ℝ) := ⟨F, hF.continuous⟩
      exact sidon_smooth_equidistribution hd hN hS hSN hm Fc K hK hF hF0 hF1 α)
  norm_num only [show (100 : ℝ) + 48000 = 48100 by norm_num] at hbound
  exact hbound

end Sidon
