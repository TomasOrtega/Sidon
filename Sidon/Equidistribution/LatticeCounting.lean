import Sidon.Equidistribution.NormalizedProgressions
import Mathlib.Data.Int.CardIntervalMod

/-! # Lattice counts for intervals and residue classes -/

noncomputable section

namespace Sidon

theorem image_int_Icc_eq_arithmeticProgression (a q lo hi : ℤ) :
    (Finset.Icc lo hi).image (fun j => a + q * j) =
      arithmeticProgression (a + q * lo) q (hi + 1 - lo).toNat := by
  classical
  by_cases hlo : lo ≤ hi
  · ext x
    simp only [Finset.mem_image, Finset.mem_Icc, arithmeticProgression, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(j - lo).toNat, by omega, ?_⟩
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ j - lo)]
      ring
    · rintro ⟨j, hj, rfl⟩
      refine ⟨lo + j, by omega, ?_⟩
      ring
  · have hlen : (hi + 1 - lo).toNat = 0 := by omega
    simp only [Finset.Icc_eq_empty_of_lt (by omega : hi < lo), Finset.image_empty,
      hlen, arithmeticProgression, Finset.range_zero]

/-- A residue class restricted to the ambient integer interval. -/
def residueClass (N : ℕ) (a q : ℤ) : Finset ℤ :=
  (interval N).filter (fun x => Int.ModEq q x a)

theorem interval_eq_Ioc (N : ℕ) : interval N = Finset.Ioc (0 : ℤ) N := by
  ext x
  simp only [interval, Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem residueClass_eq_arithmeticProgression (N : ℕ) (a q : ℤ) (hq : 0 < q) :
    ∃ b L, residueClass N a q = arithmeticProgression b q L := by
  classical
  unfold residueClass
  rw [interval_eq_Ioc, Int.Ioc_filter_modEq_eq, Int.Ioc_filter_dvd_eq _ _ hq,
    Finset.map_map]
  simp only [Finset.map_eq_image, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
  have hI (lo hi : ℤ) : Finset.Ioc lo hi = Finset.Icc (lo + 1) hi := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hI]
  simp only [zero_sub]
  have himage (lo hi : ℤ) :
      (Finset.Icc lo hi).image (fun j => j * q + a) =
        arithmeticProgression (a + q * lo) q (hi + 1 - lo).toNat := by
    simpa only [mul_comm, add_comm] using image_int_Icc_eq_arithmeticProgression a q lo hi
  change ∃ b L, (Finset.Icc _ _).image (fun j : ℤ => j * q + a) =
    arithmeticProgression b q L
  rw [himage]
  exact ⟨_, _, rfl⟩

theorem residueClass_subset_interval (N : ℕ) (a q : ℤ) : residueClass N a q ⊆ interval N :=
  Finset.filter_subset _ _

theorem residueClass_card_eq (N : ℕ) (a q : ℤ) (hq : 0 < q) :
    (residueClass N a q).card =
      Int.toNat (⌊((N : ℚ) - a) / q⌋ - ⌊(-(a : ℚ)) / q⌋) := by
  have hc := Int.Ioc_filter_modEq_card (0 : ℤ) N hq a
  rw [← interval_eq_Ioc, ← residueClass] at hc
  have hmono : ⌊(-(a : ℚ)) / q⌋ ≤ ⌊((N : ℚ) - a) / q⌋ := by
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast hq.le)
    have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith
  have hc' : ((residueClass N a q).card : ℤ) =
      ⌊((N : ℚ) - a) / q⌋ - ⌊(-(a : ℚ)) / q⌋ := by
    simpa only [Int.cast_zero, zero_sub, Int.cast_natCast, max_eq_left (sub_nonneg.mpr hmono)] using hc
  omega

theorem residueClass_card_error_le_one (N : ℕ) (a q : ℤ) (hq : 0 < q) :
    |((residueClass N a q).card : ℝ) - (N : ℝ) / q| ≤ 1 := by
  have hqrat : (0 : ℚ) < q := by exact_mod_cast hq
  have hmono : ⌊(-(a : ℚ)) / q⌋ ≤ ⌊((N : ℚ) - a) / q⌋ := by
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hqrat.le
    have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith
  have hcardint : ((residueClass N a q).card : ℤ) =
      ⌊((N : ℚ) - a) / q⌋ - ⌊(-(a : ℚ)) / q⌋ := by
    rw [residueClass_card_eq N a q hq, Int.toNat_of_nonneg (sub_nonneg.mpr hmono)]
  have hcardrat : ((residueClass N a q).card : ℚ) =
      (⌊((N : ℚ) - a) / q⌋ : ℚ) - ⌊(-(a : ℚ)) / q⌋ := by exact_mod_cast hcardint
  have hrat : |((residueClass N a q).card : ℚ) - (N : ℚ) / q| ≤ 1 := by
    rw [hcardrat, abs_le]
    have hlo := Int.floor_le ((-(a : ℚ)) / q)
    have hlo' := Int.lt_floor_add_one ((-(a : ℚ)) / q)
    have hhi := Int.floor_le (((N : ℚ) - a) / q)
    have hhi' := Int.lt_floor_add_one (((N : ℚ) - a) / q)
    have hdiff : ((N : ℚ) - a) / q - (-(a : ℚ)) / q = (N : ℚ) / q := by ring
    constructor <;> linarith
  exact_mod_cast hrat

theorem normalized_residueClass_card_error {N : ℕ} (hN : 0 < N)
    (a q : ℤ) (hq : 0 < q) :
    |((residueClass N a q).card : ℝ) / N - 1 / (q : ℝ)| ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : ((residueClass N a q).card : ℝ) / N - 1 / (q : ℝ) =
      (((residueClass N a q).card : ℝ) - (N : ℝ) / q) / N := by
    field_simp [hNpos.ne', hqpos.ne']
    ring_nf
    simp
  rw [heq, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right (residueClass_card_error_le_one N a q hq) hNpos.le

theorem int_Icc_eq_arithmeticProgression (lo hi : ℤ) :
    Finset.Icc lo hi = arithmeticProgression lo 1 (hi + 1 - lo).toNat := by
  have h := image_int_Icc_eq_arithmeticProgression 0 1 lo hi
  simp only [zero_add, one_mul] at h
  change (Finset.Icc lo hi).image id = _ at h
  simpa only [Finset.image_id] using h

theorem card_int_Icc_cast (lo hi : ℤ) :
    ((Finset.Icc lo hi).card : ℝ) = max ((hi : ℝ) + 1 - lo) 0 := by
  have h : ((Finset.Icc lo hi).card : ℤ) = max (hi + 1 - lo) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  exact_mod_cast h

/-- Integers in a scaled real interval, with independently chosen endpoint conventions. -/
def scaledInterval (N : ℕ) (a b : ℝ) (closedLeft closedRight : Bool) : Finset ℤ :=
  Finset.Icc (max 1 (if closedLeft then ⌈a * N⌉ else ⌊a * N⌋ + 1))
    (if closedRight then ⌊b * N⌋ else ⌈b * N⌉ - 1)

theorem scaledInterval_subset_interval {N : ℕ} {a b : ℝ}
    (hb : b ≤ 1) (closedLeft closedRight : Bool) :
    scaledInterval N a b closedLeft closedRight ⊆ interval N := by
  intro x hx
  rw [scaledInterval, Finset.mem_Icc] at hx
  rw [interval, Finset.mem_Icc]
  refine ⟨(le_max_left _ _).trans hx.1, ?_⟩
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hxreal : (x : ℝ) ≤ b * N := by
    cases closedRight
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx
      have hceil := Int.ceil_lt_add_one (b * N)
      have hx' : (x : ℝ) ≤ (⌈b * N⌉ : ℤ) - 1 := by exact_mod_cast hx.2
      linarith
    · simp only [↓reduceIte] at hx
      exact (by exact_mod_cast hx.2 : (x : ℝ) ≤ (⌊b * N⌋ : ℤ)).trans (Int.floor_le _)
  exact_mod_cast hxreal.trans (mul_le_of_le_one_left hN hb)

theorem mem_scaledInterval {N : ℕ} (hN : 0 < N) {a b : ℝ} (hb : b ≤ 1)
    (cl cr : Bool) (x : ℤ) :
    x ∈ scaledInterval N a b cl cr ↔ x ∈ interval N ∧
      (if cl then a ≤ (x : ℝ) / N else a < (x : ℝ) / N) ∧
      (if cr then (x : ℝ) / N ≤ b else (x : ℝ) / N < b) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : (if cl then ⌈a * N⌉ else ⌊a * N⌋ + 1) ≤ x ↔
      (if cl then a ≤ (x : ℝ) / N else a < (x : ℝ) / N) := by
    cases cl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [lt_div_iff₀ hNpos, ← Int.floor_lt]
      omega
    · simp only [↓reduceIte]
      rw [le_div_iff₀ hNpos, Int.ceil_le]
  have hright : x ≤ (if cr then ⌊b * N⌋ else ⌈b * N⌉ - 1) ↔
      (if cr then (x : ℝ) / N ≤ b else (x : ℝ) / N < b) := by
    cases cr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [div_lt_iff₀ hNpos, ← Int.lt_ceil]
      omega
    · simp only [↓reduceIte]
      rw [div_le_iff₀ hNpos, Int.le_floor]
  constructor
  · intro hx
    refine ⟨scaledInterval_subset_interval hb cl cr hx, ?_⟩
    rw [scaledInterval, Finset.mem_Icc] at hx
    exact ⟨hleft.mp ((le_max_right _ _).trans hx.1), hright.mp hx.2⟩
  · rintro ⟨hxI, hl, hr⟩
    rw [interval, Finset.mem_Icc] at hxI
    rw [scaledInterval, Finset.mem_Icc]
    exact ⟨max_le hxI.1 (hleft.mpr hl), hright.mpr hr⟩


theorem scaledInterval_is_arithmeticProgression (N : ℕ) (a b : ℝ) (cl cr : Bool) :
    ∃ c L, scaledInterval N a b cl cr = arithmeticProgression c 1 L := by
  unfold scaledInterval
  rw [int_Icc_eq_arithmeticProgression]
  exact ⟨_, _, rfl⟩

theorem scaledInterval_card_error_le_one {N : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (cl cr : Bool) :
    |((scaledInterval N a b cl cr).card : ℝ) - (b - a) * N| ≤ 1 := by
  let lo : ℤ := max 1 (if cl then ⌈a * N⌉ else ⌊a * N⌋ + 1)
  let hi : ℤ := if cr then ⌊b * N⌋ else ⌈b * N⌉ - 1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hapos : 0 ≤ a * N := mul_nonneg ha hN
  have hlo : a * N ≤ lo ∧ (lo : ℝ) ≤ a * N + 1 := by
    dsimp [lo]
    rw [Int.cast_max, Int.cast_one]
    cases cl <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_one]
    · have hfloor := Int.floor_le (a * N)
      have hfloor' := Int.lt_floor_add_one (a * N)
      constructor
      · exact hfloor'.le.trans (le_max_right _ _)
      · exact max_le (by linarith) (by linarith)
    · have hceil := Int.le_ceil (a * N)
      have hceil' := Int.ceil_lt_add_one (a * N)
      constructor
      · exact hceil.trans (le_max_right _ _)
      · exact max_le (by linarith) hceil'.le
  have hhi : b * N - 1 ≤ hi ∧ (hi : ℝ) ≤ b * N := by
    dsimp [hi]
    cases cr <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_one]
    · have hceil := Int.le_ceil (b * N)
      have hceil' := Int.ceil_lt_add_one (b * N)
      constructor <;> linarith
    · have hfloor := Int.floor_le (b * N)
      have hfloor' := Int.lt_floor_add_one (b * N)
      constructor <;> linarith
  have hlength : 0 ≤ (b - a) * N := mul_nonneg (sub_nonneg.mpr hab) hN
  change |((Finset.Icc lo hi).card : ℝ) - (b - a) * N| ≤ 1
  rw [card_int_Icc_cast]
  by_cases hr : 0 ≤ (hi : ℝ) + 1 - lo
  · rw [max_eq_left hr, abs_le]
    constructor <;> nlinarith [hlo.1, hlo.2, hhi.1, hhi.2]
  · rw [max_eq_right (not_le.mp hr).le, zero_sub, abs_neg, abs_of_nonneg hlength]
    nlinarith [hlo.1, hlo.2, hhi.1, hhi.2]

theorem normalized_scaledInterval_card_error {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (cl cr : Bool) :
    |((scaledInterval N a b cl cr).card : ℝ) / N - (b - a)| ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : ((scaledInterval N a b cl cr).card : ℝ) / N - (b - a) =
      (((scaledInterval N a b cl cr).card : ℝ) - (b - a) * N) / N := by
    field_simp [hNpos.ne']
    ring
  rw [heq, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right (scaledInterval_card_error_le_one ha hab cl cr) hNpos.le

end Sidon
