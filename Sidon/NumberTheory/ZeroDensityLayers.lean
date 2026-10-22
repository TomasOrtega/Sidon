import Sidon.NumberTheory.ZeroLayers
import Sidon.NumberTheory.ZetaZeroCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform zero density bounds imply finite weighted-zero bounds -/

noncomputable section

namespace Sidon

variable {ι : Type*}

theorem zeroLayer_card_le_of_density (s : Finset ι) (β : ι → ℝ)
    {L K D : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hβ : ∀ i ∈ s, 0 ≤ β i ∧ β i ≤ 1)
    (hcount : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      ((s.filter (fun i => σ ≤ β i)).card : ℝ) ≤ K * Real.exp (D * (1 - σ)))
    (j : ℕ) :
    ((zeroLayer s β L j).card : ℝ) ≤ K * Real.exp ((D / L) * (j + 1)) := by
  classical
  let σ : ℝ := max 0 (1 - ((j : ℝ) + 1) / L)
  have hσ0 : 0 ≤ σ := le_max_left _ _
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    apply max_le (by norm_num)
    have := div_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity) hL.le
    linarith
  have hsub : zeroLayer s β L j ⊆ s.filter (fun i => σ ≤ β i) := by
    intro i hi
    obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨his, ?_⟩
    dsimp [σ]
    apply max_le (hβ i his).1
    have hdist : 0 ≤ L * (1 - β i) := mul_nonneg hL.le (by linarith [(hβ i his).2])
    have hf := Nat.lt_floor_add_one (L * (1 - β i))
    rw [hij] at hf
    have hh : 1 - β i < ((j : ℝ) + 1) / L := (lt_div_iff₀ hL).mpr (by nlinarith)
    linarith
  have hDσ : D * (1 - σ) ≤ (D / L) * ((j : ℝ) + 1) := by
    have hmax : 1 - ((j : ℝ) + 1) / L ≤ σ := le_max_right _ _
    have hh : 1 - σ ≤ ((j : ℝ) + 1) / L := by linarith
    have := mul_le_mul_of_nonneg_left hh hD
    convert this using 1; ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((hcount σ hσ0 hσ1).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hDσ) hK))

/-- Density bounds hold at a moving real part; uniform constants are essential. -/
theorem finite_zero_bound_of_density (s : Finset ι) (β : ι → ℝ)
    {L η K D : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hDL : D < L)
    (hβ0 : ∀ i ∈ s, 0 ≤ β i)
    (hβ1 : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      ((s.filter (fun i => σ ≤ β i)).card : ℝ) ≤ K * Real.exp (D * (1 - σ))) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp (D / L)) *
        Real.exp (-(1 - D / L) * Nat.floor (L * η)) /
        (1 - Real.exp (-(1 - D / L))) := by
  apply finite_zero_layer_bound s β hL hη hK ((div_lt_one hL).mpr hDL) hβ1
  intro j
  apply zeroLayer_card_le_of_density s β hL hK hD _ hcount j
  intro i hi
  exact ⟨hβ0 i hi, by linarith [hβ1 i hi]⟩

/-- A logarithmic zero-free reserve absorbs a fixed logarithmic density loss. -/
theorem finite_zero_bound_of_log_reserve (s : Finset ι) (β : ι → ℝ)
    {L η K b : ℝ} {B : ℕ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hb : b < 1)
    (hβ : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ j : ℕ, ((zeroLayer s β L j).card : ℝ) ≤
      (K * L ^ B) * Real.exp (b * (j + 1)))
    (hreserve : ((B : ℝ) + 2) * Real.log L ≤
      (1 - b) * Nat.floor (L * η)) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp b) / (1 - Real.exp (-(1 - b))) / L ^ 2 := by
  have hden : 0 < 1 - Real.exp (-(1 - b)) := by
    have := Real.exp_lt_one_iff.mpr (show -(1 - b) < 0 by linarith)
    linarith
  have hexp : Real.exp (-(1 - b) * Nat.floor (L * η)) ≤ (L ^ (B + 2))⁻¹ := by
    calc
      _ ≤ Real.exp (-(((B : ℝ) + 2) * Real.log L)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, show ((B : ℝ) + 2) = ((B + 2 : ℕ) : ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log hL]
  have hh := finite_zero_layer_bound s β hL hη
    (mul_nonneg hK (pow_nonneg hL.le B)) hb hβ hcount
  apply hh.trans
  calc
    _ ≤ ((K * L ^ B) * Real.exp b) * (L ^ (B + 2))⁻¹ /
        (1 - Real.exp (-(1 - b))) := by gcongr
    _ = _ := by
      rw [pow_add, pow_two]
      field_simp

/-- A multiplicity-sensitive bound for the actual positive-height zeta zeros. -/
theorem zeta_zero_weight_bound {A K T₀ T x η : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hT : 1 < T) (hx : 1 < x) (hT₀ : T₀ ≤ T)
    (hη : 0 ≤ η) (hscale : A * Real.log T < Real.log x)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ∀ z ∈ zetaZeroOccurrences T, z.1.re ≤ 1 - η) :
    (∑ z ∈ zetaZeroOccurrences T, x ^ (z.1.re - 1)) ≤
      ((K * (Real.log T) ^ B) * Real.exp (A * Real.log T / Real.log x)) *
        Real.exp (-(1 - A * Real.log T / Real.log x) * Nat.floor (Real.log x * η)) /
        (1 - Real.exp (-(1 - A * Real.log T / Real.log x))) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD : 0 ≤ A * Real.log T := mul_nonneg hA (Real.log_pos hT).le
  have hcount (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
      (((zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re)).card : ℝ) ≤
        (K * (Real.log T) ^ B) * Real.exp ((A * Real.log T) * (1 - σ)) := by
    have hh := hdensity T hT₀ σ hσ0 hσ1
    change (zetaZeroCount σ T : ℝ) ≤ _
    convert hh using 1
    rw [Real.rpow_def_of_pos (by linarith : 0 < T)]
    ring_nf
  have hh := finite_zero_bound_of_density (zetaZeroOccurrences T) (fun z => z.1.re)
    hL hη (mul_nonneg hK (pow_nonneg (Real.log_pos hT).le B)) hD hscale
    (fun z hz => (zetaZeroOccurrences_re_bounds hz).1) hfree hcount
  convert hh using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  congr 1
  ring

end Sidon
