import Sidon.Combinatorics.Intervals
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

/-! # Finite Bohr sets and denominator-free regularity -/

noncomputable section

namespace Sidon

/-- A finite Bohr set, using the maximum norm on the product torus. -/
def bohrSet {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) : Finset ℤ :=
  (interval N).filter fun x => ‖x • α‖ ≤ ρ

@[simp]
theorem mem_bohrSet {d N : ℕ} {α : Fin d → AddCircle (1 : ℝ)} {ρ : ℝ} {x : ℤ} :
    x ∈ bohrSet N α ρ ↔ x ∈ interval N ∧ ‖x • α‖ ≤ ρ := Finset.mem_filter

theorem bohrSet_subset_interval {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ))
    (ρ : ℝ) : bohrSet N α ρ ⊆ interval N := Finset.filter_subset _ _

theorem card_bohrSet_le {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) :
    (bohrSet N α ρ).card ≤ N := by
  simpa only [card_interval] using Finset.card_le_card (bohrSet_subset_interval N α ρ)

theorem bohrSet_mono {d N : ℕ} (α : Fin d → AddCircle (1 : ℝ)) {ρ σ : ℝ}
    (hρσ : ρ ≤ σ) : bohrSet N α ρ ⊆ bohrSet N α σ := by
  intro x hx
  exact mem_bohrSet.mpr ⟨(mem_bohrSet.mp hx).1, (mem_bohrSet.mp hx).2.trans hρσ⟩

theorem bohrSet_eq_empty_of_neg {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ))
    {ρ : ℝ} (hρ : ρ < 0) : bohrSet N α ρ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := (mem_bohrSet.mp hx).2
  exact (not_le_of_gt hρ) ((norm_nonneg _).trans h)

/-- Regularity is stated without division by the size of the Bohr set. -/
def IsRegularBohrSet {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) : Prop :=
  ∀ κ : ℝ, |κ| ≤ 1 / (100 * (d : ℝ)) →
    |((bohrSet N α ((1 + κ) * ρ)).card : ℝ) - (bohrSet N α ρ).card| ≤
      100 * (d : ℝ) * |κ| * (bohrSet N α ρ).card

/-- At a nonempty Bohr set this agrees with the ratio formulation in the paper. -/
theorem isRegularBohrSet_iff_ratio {d N : ℕ} {α : Fin d → AddCircle (1 : ℝ)} {ρ : ℝ}
    (hB : 0 < (bohrSet N α ρ).card) : IsRegularBohrSet N α ρ ↔
    ∀ κ : ℝ, |κ| ≤ 1 / (100 * (d : ℝ)) →
      |((bohrSet N α ((1 + κ) * ρ)).card : ℝ) / (bohrSet N α ρ).card - 1| ≤
        100 * (d : ℝ) * |κ| := by
  have hBr : (0 : ℝ) < (bohrSet N α ρ).card := Nat.cast_pos.mpr hB
  have heq (a : ℝ) : |a / (bohrSet N α ρ).card - 1| =
      |a - (bohrSet N α ρ).card| / (bohrSet N α ρ).card := by
    have hsub : a / (bohrSet N α ρ).card - 1 =
        (a - (bohrSet N α ρ).card) / (bohrSet N α ρ).card := by
      field_simp
    rw [hsub, abs_div, abs_of_pos hBr]
  constructor
  · intro h κ hκ
    rw [heq]
    exact (div_le_iff₀ hBr).mpr (h κ hκ)
  · intro h κ hκ
    have hh := h κ hκ
    rw [heq] at hh
    exact (div_le_iff₀ hBr).mp hh

theorem norm_torus_le_half {d : ℕ} (β : Fin d → AddCircle (1 : ℝ)) :
    ‖β‖ ≤ (1 / 2 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  simpa using (AddCircle.norm_le_half_period (1 : ℝ) (x := β i) (by norm_num))

theorem bohrSet_eq_interval_of_half_le {d : ℕ} (N : ℕ)
    (α : Fin d → AddCircle (1 : ℝ)) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) :
    bohrSet N α ρ = interval N := by
  apply Finset.filter_eq_self.mpr
  intro x _
  exact (norm_torus_le_half (x • α)).trans hρ

/-- A radial linear cutoff, clipped to the unit interval. -/
def clippedNormRamp {E : Type*} [SeminormedAddCommGroup E] (r t : ℝ) (x : E) : ℝ :=
  min 1 (max 0 ((r - ‖x‖) / t))

theorem clippedNormRamp_nonneg {E : Type*} [SeminormedAddCommGroup E]
    (r t : ℝ) (x : E) : 0 ≤ clippedNormRamp r t x := by
  exact le_min (by norm_num) (le_max_left _ _)

theorem clippedNormRamp_le_one {E : Type*} [SeminormedAddCommGroup E]
    (r t : ℝ) (x : E) : clippedNormRamp r t x ≤ 1 := min_le_left _ _

theorem clippedNormRamp_eq_one {E : Type*} [SeminormedAddCommGroup E]
    {r t : ℝ} (ht : 0 < t) {x : E} (hx : ‖x‖ ≤ r - t) :
    clippedNormRamp r t x = 1 := by
  have hraw : (1 : ℝ) ≤ (r - ‖x‖) / t := (le_div_iff₀ ht).mpr (by linarith)
  exact min_eq_left (hraw.trans (le_max_right _ _))

theorem clippedNormRamp_eq_zero {E : Type*} [SeminormedAddCommGroup E]
    {r t : ℝ} (ht : 0 < t) {x : E} (hx : r ≤ ‖x‖) :
    clippedNormRamp r t x = 0 := by
  have hraw : (r - ‖x‖) / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le
  simp only [clippedNormRamp, max_eq_left hraw, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem lipschitzWith_clippedNormRamp {E : Type*} [SeminormedAddCommGroup E]
    (r : ℝ) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) (clippedNormRamp r t : E → ℝ) := by
  have hraw : LipschitzWith (Real.toNNReal t⁻¹) (fun x : E => (r - ‖x‖) / t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hn : |‖x‖ - ‖y‖| ≤ dist x y := by
      simpa only [dist_zero_right, NNReal.coe_one, one_mul, Real.dist_eq] using
        (LipschitzWith.dist_left (0 : E)).dist_le_mul x y
    have heq : (r - ‖x‖) / t - (r - ‖y‖) / t = -(‖x‖ - ‖y‖) / t := by ring
    rw [Real.dist_eq, heq, abs_div, abs_neg, abs_of_pos ht]
    calc
      |‖x‖ - ‖y‖| / t ≤ dist x y / t := div_le_div_of_nonneg_right hn ht.le
      _ = (Real.toNNReal t⁻¹ : ℝ) * dist x y := by
        rw [Real.coe_toNNReal t⁻¹ (inv_nonneg.mpr ht.le)]
        ring
  have hclip : LipschitzWith 1 (fun z : ℝ => min 1 (max 0 z)) :=
    (LipschitzWith.id.const_max 0).const_min 1
  change LipschitzWith (Real.toNNReal t⁻¹) (fun x : E => min 1 (max 0 ((r - ‖x‖) / t)))
  simpa only [one_mul, Function.comp_def] using hclip.comp hraw

theorem indicator_le_clippedNormRamp {E : Type*} [SeminormedAddCommGroup E]
    {r t : ℝ} (ht : 0 < t) (x : E) :
    (if ‖x‖ ≤ r - t then (1 : ℝ) else 0) ≤ clippedNormRamp r t x := by
  split_ifs with hx
  · rw [clippedNormRamp_eq_one ht hx]
  · exact clippedNormRamp_nonneg r t x

theorem clippedNormRamp_le_indicator {E : Type*} [SeminormedAddCommGroup E]
    {r t : ℝ} (ht : 0 < t) (x : E) :
    clippedNormRamp r t x ≤ if ‖x‖ ≤ r then (1 : ℝ) else 0 := by
  split_ifs with hx
  · exact clippedNormRamp_le_one r t x
  · rw [clippedNormRamp_eq_zero ht (le_of_not_ge hx)]

theorem IsRegularBohrSet.card_add_radius_le {d N : ℕ}
    {α : Fin d → AddCircle (1 : ℝ)} {ρ t : ℝ} (hreg : IsRegularBohrSet N α ρ)
    (hd : 0 < d) (hρ : 0 < ρ) (ht : 0 ≤ t) (hsmall : t ≤ ρ / (100 * (d : ℝ))) :
    |((bohrSet N α (ρ + t)).card : ℝ) - (bohrSet N α ρ).card| ≤
      100 * (d : ℝ) * (t / ρ) * (bohrSet N α ρ).card := by
  have hd' : (0 : ℝ) < 100 * (d : ℝ) := by positivity
  have hκ₀ : 0 ≤ t / ρ := div_nonneg ht hρ.le
  have hκ : |t / ρ| ≤ 1 / (100 * (d : ℝ)) := by
    rw [abs_of_nonneg hκ₀]
    apply (div_le_div_iff₀ hρ hd').mpr
    simpa only [one_mul] using (le_div_iff₀ hd').mp hsmall
  have h := hreg (t / ρ) hκ
  have hradius : (1 + t / ρ) * ρ = ρ + t := by field_simp
  simpa only [hradius, abs_of_nonneg hκ₀] using h

theorem IsRegularBohrSet.card_sub_radius_le {d N : ℕ}
    {α : Fin d → AddCircle (1 : ℝ)} {ρ t : ℝ} (hreg : IsRegularBohrSet N α ρ)
    (hd : 0 < d) (hρ : 0 < ρ) (ht : 0 ≤ t) (hsmall : t ≤ ρ / (100 * (d : ℝ))) :
    |((bohrSet N α (ρ - t)).card : ℝ) - (bohrSet N α ρ).card| ≤
      100 * (d : ℝ) * (t / ρ) * (bohrSet N α ρ).card := by
  have hd' : (0 : ℝ) < 100 * (d : ℝ) := by positivity
  have hκ₀ : 0 ≤ t / ρ := div_nonneg ht hρ.le
  have hκ : |-(t / ρ)| ≤ 1 / (100 * (d : ℝ)) := by
    rw [abs_neg, abs_of_nonneg hκ₀]
    apply (div_le_div_iff₀ hρ hd').mpr
    simpa only [one_mul] using (le_div_iff₀ hd').mp hsmall
  have h := hreg (-(t / ρ)) hκ
  have hradius : (1 + -(t / ρ)) * ρ = ρ - t := by field_simp; ring
  simpa only [hradius, abs_neg, abs_of_nonneg hκ₀] using h

theorem IsRegularBohrSet.normalized_card_add_radius_le {d N : ℕ}
    {α : Fin d → AddCircle (1 : ℝ)} {ρ t : ℝ} (hreg : IsRegularBohrSet N α ρ)
    (hN : 0 < N) (hd : 0 < d) (hρ : 0 < ρ) (ht : 0 ≤ t)
    (hsmall : t ≤ ρ / (100 * (d : ℝ))) :
    |((bohrSet N α (ρ + t)).card : ℝ) / N - (bohrSet N α ρ).card / N| ≤
      100 * (d : ℝ) * (t / ρ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcard : ((bohrSet N α ρ).card : ℝ) ≤ N := by exact_mod_cast card_bohrSet_le N α ρ
  rw [← sub_div, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  exact (hreg.card_add_radius_le hd hρ ht hsmall).trans
    (mul_le_mul_of_nonneg_left hcard (by positivity))

theorem IsRegularBohrSet.normalized_card_sub_radius_le {d N : ℕ}
    {α : Fin d → AddCircle (1 : ℝ)} {ρ t : ℝ} (hreg : IsRegularBohrSet N α ρ)
    (hN : 0 < N) (hd : 0 < d) (hρ : 0 < ρ) (ht : 0 ≤ t)
    (hsmall : t ≤ ρ / (100 * (d : ℝ))) :
    |((bohrSet N α (ρ - t)).card : ℝ) / N - (bohrSet N α ρ).card / N| ≤
      100 * (d : ℝ) * (t / ρ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcard : ((bohrSet N α ρ).card : ℝ) ≤ N := by exact_mod_cast card_bohrSet_le N α ρ
  rw [← sub_div, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  exact (hreg.card_sub_radius_le hd hρ ht hsmall).trans
    (mul_le_mul_of_nonneg_left hcard (by positivity))

end Sidon
