module

public import Sidon.Equidistribution.Bohr
public import Mathlib.Algebra.Order.BigOperators.Expect

@[expose] public section

/-! # Comparing finite Bohr counts with Lipschitz orbit averages -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem bohr_discrepancy_le_one {d : ℕ} (N : ℕ) (S : Finset ℤ)
    (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤ 1 := by
  have hleft₀ : (0 : ℝ) ≤ ((S ∩ bohrSet N α ρ).card : ℝ) / S.card := by positivity
  have hright₀ : (0 : ℝ) ≤ ((bohrSet N α ρ).card : ℝ) / N := by positivity
  have hleft : ((S ∩ bohrSet N α ρ).card : ℝ) / S.card ≤ 1 := by
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : S ∩ bohrSet N α ρ ⊆ S)
  have hright : ((bohrSet N α ρ).card : ℝ) / N ≤ 1 := by
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast card_bohrSet_le N α ρ
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem expect_bohr_indicator {d N : ℕ} (S : Finset ℤ) (hSN : S ⊆ interval N)
    (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) :
    (𝔼 x ∈ S, if ‖x • α‖ ≤ ρ then (1 : ℝ) else 0) =
      ((S ∩ bohrSet N α ρ).card : ℝ) / S.card := by
  classical
  rw [Finset.expect_eq_sum_div_card]
  congr 1
  have heq : S.filter (fun x => ‖x • α‖ ≤ ρ) = S ∩ bohrSet N α ρ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, mem_bohrSet]
    exact ⟨fun h => ⟨h.1, hSN h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [← heq]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]

theorem expect_bohr_indicator_interval {d : ℕ} (N : ℕ)
    (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) :
    (𝔼 x ∈ interval N, if ‖x • α‖ ≤ ρ then (1 : ℝ) else 0) =
      ((bohrSet N α ρ).card : ℝ) / N := by
  rw [expect_bohr_indicator (interval N) (fun _ h => h), card_interval,
    Finset.inter_eq_right.mpr (bohrSet_subset_interval N α ρ)]

theorem bohr_discrepancy_le_cutoff_errors {d N : ℕ} (S : Finset ℤ)
    (hSN : S ⊆ interval N) (α : Fin d → AddCircle (1 : ℝ)) {ρ t D B : ℝ}
    (ht : 0 < t)
    (hupper : |(𝔼 x ∈ S, clippedNormRamp (ρ + t) t (x • α)) -
      (𝔼 x ∈ interval N, clippedNormRamp (ρ + t) t (x • α))| ≤ D)
    (hlower : |(𝔼 x ∈ S, clippedNormRamp ρ t (x • α)) -
      (𝔼 x ∈ interval N, clippedNormRamp ρ t (x • α))| ≤ D)
    (hBupper : ((bohrSet N α (ρ + t)).card : ℝ) / N - (bohrSet N α ρ).card / N ≤ B)
    (hBlower : ((bohrSet N α ρ).card : ℝ) / N - (bohrSet N α (ρ - t)).card / N ≤ B) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤ D + B := by
  have hSupper : ((S ∩ bohrSet N α ρ).card : ℝ) / S.card ≤
      𝔼 x ∈ S, clippedNormRamp (ρ + t) t (x • α) := by
    rw [← expect_bohr_indicator S hSN α ρ]
    apply Finset.expect_le_expect
    intro x _
    have hr : ρ + t - t = ρ := by ring
    simpa only [hr] using
      (indicator_le_clippedNormRamp (r := ρ + t) ht (x • α))
  have hSlower : (𝔼 x ∈ S, clippedNormRamp ρ t (x • α)) ≤
      ((S ∩ bohrSet N α ρ).card : ℝ) / S.card := by
    rw [← expect_bohr_indicator S hSN α ρ]
    exact Finset.expect_le_expect fun x _ => clippedNormRamp_le_indicator ht (x • α)
  have hIupper : (𝔼 x ∈ interval N, clippedNormRamp (ρ + t) t (x • α)) ≤
      ((bohrSet N α (ρ + t)).card : ℝ) / N := by
    rw [← expect_bohr_indicator_interval N α (ρ + t)]
    exact Finset.expect_le_expect fun x _ => clippedNormRamp_le_indicator ht (x • α)
  have hIlower : ((bohrSet N α (ρ - t)).card : ℝ) / N ≤
      𝔼 x ∈ interval N, clippedNormRamp ρ t (x • α) := by
    rw [← expect_bohr_indicator_interval N α (ρ - t)]
    exact Finset.expect_le_expect fun x _ => indicator_le_clippedNormRamp ht (x • α)
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hlower).1],
    by linarith [(abs_le.mp hupper).2]⟩

theorem IsRegularBohrSet.discrepancy_le_cutoff_errors {d N : ℕ}
    {α : Fin d → AddCircle (1 : ℝ)} {ρ t D : ℝ} (hreg : IsRegularBohrSet N α ρ)
    (S : Finset ℤ) (hSN : S ⊆ interval N) (hN : 0 < N) (hd : 0 < d)
    (hρ : 0 < ρ) (ht : 0 < t) (hsmall : t ≤ ρ / (100 * (d : ℝ)))
    (hupper : |(𝔼 x ∈ S, clippedNormRamp (ρ + t) t (x • α)) -
      (𝔼 x ∈ interval N, clippedNormRamp (ρ + t) t (x • α))| ≤ D)
    (hlower : |(𝔼 x ∈ S, clippedNormRamp ρ t (x • α)) -
      (𝔼 x ∈ interval N, clippedNormRamp ρ t (x • α))| ≤ D) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤
      D + 100 * (d : ℝ) * (t / ρ) := by
  apply bohr_discrepancy_le_cutoff_errors S hSN α ht hupper hlower
  · exact (le_abs_self _).trans (hreg.normalized_card_add_radius_le hN hd hρ ht.le hsmall)
  · have hb := hreg.normalized_card_sub_radius_le hN hd hρ ht.le hsmall
    rw [abs_sub_comm] at hb
    exact (le_abs_self _).trans hb

end Sidon
