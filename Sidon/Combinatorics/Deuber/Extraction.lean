module

public import Sidon.Combinatorics.Deuber.Basic
public import Sidon.Combinatorics.Deuber.Containment
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot

@[expose] public section

/-! # The Hales--Jewett bridge and the block maps used in Deuber extraction -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.Deuber

theorem exists_fin_wordLength (α : Type*) [Finite α] (r : ℕ) (hr : 0 < r) :
    ∃ h : ℕ, 0 < h ∧ ∀ χ : (Fin h → α) → Fin r,
      ∃ l : Combinatorics.Line α (Fin h), l.IsMono χ := by
  classical
  obtain ⟨ι, inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension α (Fin r)
  have hpos : 0 < Fintype.card ι := by
    obtain ⟨l, _⟩ := hι (fun _ => ⟨0, hr⟩)
    obtain ⟨i, _⟩ := l.proper
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  refine ⟨Fintype.card ι, hpos, ?_⟩
  intro χ
  let e := Fintype.equivFin ι
  obtain ⟨l, colour, hcolour⟩ := hι (fun v => χ (v ∘ e.symm))
  let l' : Combinatorics.Line α (Fin (Fintype.card ι)) :=
    { idxFun := l.idxFun ∘ e.symm
      proper := by
        obtain ⟨i, hi⟩ := l.proper
        exact ⟨e i, by simpa using hi⟩ }
  exact ⟨l', colour, hcolour⟩

abbrev WordSource (ι δ β : Type*) := (ι × δ) ⊕ Option β

abbrev WordTarget (δ β : Type*) := δ ⊕ Option β

/-- A variable source coordinate feeds its early row; a fixed one feeds the middle row. -/
def wordActiveRow {ι δ β : Type*} {p : ℕ}
    (l : Combinatorics.Line (δ → Coeff p) ι) : WordSource ι δ β → WordTarget δ β
  | Sum.inl (i, t) => if l.idxFun i = none then Sum.inl t else Sum.inr none
  | Sum.inr v => Sum.inr v

def wordWeight {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) : WordSource ι δ β → ℤ
  | Sum.inl (i, t) => (l.idxFun i).elim c fun a => (a t : ℤ)
  | Sum.inr _ => c

/-- The generator change in one Hales--Jewett row-focusing step. -/
def wordMatrix {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) :
    Matrix (WordTarget δ β) (WordSource ι δ β) ℤ :=
  fun i j => if i = wordActiveRow l j then wordWeight c l j else 0

theorem wordMatrix_isBlockEmbedding {ι δ β : Type*} {p : ℕ} {c : ℤ}
    (hc : c ≠ 0) (l : Combinatorics.Line (δ → Coeff p) ι) :
    IsBlockEmbedding (wordMatrix (β := β) c l) := by
  classical
  constructor
  · intro i
    rcases i with t | v
    · obtain ⟨a, ha⟩ := l.proper
      exact ⟨Sum.inl (a, t), by simp [wordMatrix, wordActiveRow, wordWeight, ha, hc]⟩
    · exact ⟨Sum.inr v, by simp [wordMatrix, wordActiveRow, wordWeight, hc]⟩
  · intro i i' j hii'
    by_cases hi : i = wordActiveRow l j
    · right
      have hi' : i' ≠ wordActiveRow l j := by
        intro hi'
        exact hii' (hi.trans hi'.symm)
      simp [wordMatrix, hi']
    · exact Or.inl (by simp [wordMatrix, hi])

theorem wordMatrices_finite {ι δ β : Type*} [Fintype ι] [Fintype δ] [Fintype β]
    (p : ℕ) (c : ℤ) :
    (Set.range (wordMatrix (ι := ι) (δ := δ) (β := β) (p := p) c)).Finite := by
  have hinj : Function.Injective
      (Combinatorics.Line.idxFun : Combinatorics.Line (δ → Coeff p) ι →
        ι → Option (δ → Coeff p)) := by
    intro l l' h
    cases l
    cases l'
    cases h
    rfl
  letI : Finite (Combinatorics.Line (δ → Coeff p) ι) := Finite.of_injective _ hinj
  exact Set.finite_range _

theorem wordMatrix_early_prefix {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (t u : δ) (i : ι) :
    wordMatrix (β := β) c l (Sum.inl t) (Sum.inl (i, u)) =
      if l.idxFun i = none ∧ t = u then c else 0 := by
  cases h : l.idxFun i <;> simp [wordMatrix, wordActiveRow, wordWeight, h]

@[simp]
theorem wordMatrix_early_extra {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (t : δ) (v : Option β) :
    wordMatrix c l (Sum.inl t) (Sum.inr v) = 0 := by
  simp [wordMatrix, wordActiveRow]

theorem wordMatrix_middle_prefix {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (i : ι) (t : δ) :
    wordMatrix (β := β) c l (Sum.inr none) (Sum.inl (i, t)) =
      (l.idxFun i).elim 0 fun a => (a t : ℤ) := by
  cases h : l.idxFun i <;> simp [wordMatrix, wordActiveRow, wordWeight, h]

@[simp]
theorem wordMatrix_late_prefix {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (v : β) (i : ι) (t : δ) :
    wordMatrix c l (Sum.inr (some v)) (Sum.inl (i, t)) = 0 := by
  cases h : l.idxFun i <;> simp [wordMatrix, wordActiveRow, wordWeight, h]

theorem wordMatrix_extra {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (v v' : Option β) :
    wordMatrix c l (Sum.inr v) (Sum.inr v') = if v = v' then c else 0 := by
  simp [wordMatrix, wordActiveRow, wordWeight]

theorem wordMatrix_mulVec_early {ι δ β : Type*} [Fintype ι] [Fintype δ] [Fintype β]
    {p : ℕ} (c : ℤ) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) (t : δ) :
    (wordMatrix c l).mulVec S (Sum.inl t) =
      c * ∑ i ∈ Finset.univ.filter (fun i => l.idxFun i = none), S (Sum.inl (i, t)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    wordMatrix_early_prefix, wordMatrix_early_extra, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : l.idxFun i = none
  · simp [hi, Finset.sum_filter]
  · simp [hi, Finset.sum_filter]

theorem wordMatrix_mulVec_middle {ι δ β : Type*} [Fintype ι] [Fintype δ] [Fintype β]
    {p : ℕ} (c : ℤ) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) :
    (wordMatrix c l).mulVec S (Sum.inr none) =
      (∑ i, ∑ t, ((l.idxFun i).elim 0 fun a => (a t : ℤ)) * S (Sum.inl (i, t))) +
        c * S (Sum.inr none) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    wordMatrix_middle_prefix, wordMatrix_extra]

theorem wordMatrix_mulVec_late {ι δ β : Type*} [Fintype ι] [Fintype δ] [Fintype β]
    {p : ℕ} (c : ℤ) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) (v : β) :
    (wordMatrix c l).mulVec S (Sum.inr (some v)) = c * S (Sum.inr (some v)) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    wordMatrix_extra]

def focusedCoeff {δ β : Type*} {p : ℕ} (c : ℤ) (a : δ → Coeff p) : WordTarget δ β → ℤ
  | Sum.inl t => (a t : ℤ)
  | Sum.inr none => c
  | Sum.inr (some _) => 0

theorem focusedCoeff_vecMul_wordMatrix {ι δ β : Type*} [Fintype δ] [Fintype β]
    {p : ℕ} (c : ℤ) (l : Combinatorics.Line (δ → Coeff p) ι)
    (a : δ → Coeff p) :
    Matrix.vecMul (focusedCoeff (β := β) c a) (wordMatrix c l) =
      fun j => match j with
        | Sum.inl (i, t) => c * ((l a i) t : ℤ)
        | Sum.inr none => c ^ 2
        | Sum.inr (some _) => 0 := by
  funext j
  rcases j with ⟨i, t⟩ | v
  · cases h : l.idxFun i <;>
      simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, focusedCoeff,
        wordMatrix_early_prefix, wordMatrix_middle_prefix, Combinatorics.Line.coe_apply,
        h, mul_comm]
  · cases v <;>
      simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, focusedCoeff,
        wordMatrix_extra, pow_two]

def wordEvaluation {ι δ β : Type*} [Fintype ι] [Fintype δ] {p : ℕ} (c : ℤ)
    (S : WordSource ι δ β → ℤ) (a : ι → δ → Coeff p) : ℤ :=
  c * (∑ i, ∑ t, (a i t : ℤ) * S (Sum.inl (i, t))) + c ^ 2 * S (Sum.inr none)

theorem focusedRow_eq_wordEvaluation {ι δ β : Type*}
    [Fintype ι] [Fintype δ] [Fintype β] {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (S : WordSource ι δ β → ℤ)
    (a : δ → Coeff p) :
    c * (wordMatrix c l).mulVec S (Sum.inr none) +
        (∑ t, (a t : ℤ) * (wordMatrix c l).mulVec S (Sum.inl t)) =
      wordEvaluation c S (l a) := by
  have h := Matrix.dotProduct_mulVec (focusedCoeff (β := β) c a) (wordMatrix c l) S
  rw [focusedCoeff_vecMul_wordMatrix] at h
  simpa [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    focusedCoeff, wordEvaluation, Finset.mul_sum, mul_assoc, add_comm] using h

theorem focusedRow_isMonochromatic {ι δ β : Type*}
    [Fintype ι] [Fintype δ] [Fintype β] {κ : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (S : WordSource ι δ β → ℤ)
    (χ : ℤ → κ) (hl : l.IsMono (fun a => χ (wordEvaluation c S a))) :
    ∃ colour, ∀ a : δ → Coeff p,
      χ (c * (wordMatrix c l).mulVec S (Sum.inr none) +
        (∑ t, (a t : ℤ) * (wordMatrix c l).mulVec S (Sum.inl t))) = colour := by
  obtain ⟨colour, hcolour⟩ := hl
  refine ⟨colour, fun a => ?_⟩
  rw [focusedRow_eq_wordEvaluation]
  exact hcolour a

theorem exists_focused_block_row (δ β : Type*) [Fintype δ] [Fintype β]
    (p r : ℕ) (c : ℤ) (hr : 0 < r) (hc : c ≠ 0) :
    ∃ h : ℕ, 0 < h ∧ ∃ family : Set
      (Matrix (WordTarget δ β) (WordSource (Fin h) δ β) ℤ),
      family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
      ∀ (S : WordSource (Fin h) δ β → ℤ) (χ : ℤ → Fin r),
        ∃ T ∈ family, ∃ colour, ∀ a : δ → Coeff p,
          χ (c * T.mulVec S (Sum.inr none) +
            (∑ t, (a t : ℤ) * T.mulVec S (Sum.inl t))) = colour := by
  obtain ⟨h, hpos, hh⟩ := exists_fin_wordLength (δ → Coeff p) r hr
  refine ⟨h, hpos, Set.range (wordMatrix (ι := Fin h) (δ := δ) (β := β) (p := p) c),
    wordMatrices_finite p c, ?_, ?_⟩
  · rintro T ⟨l, rfl⟩
    exact wordMatrix_isBlockEmbedding hc l
  · intro S χ
    obtain ⟨l, hl⟩ := hh (fun a => χ (wordEvaluation c S a))
    exact ⟨wordMatrix c l, ⟨l, rfl⟩, focusedRow_isMonochromatic c l S χ hl⟩

theorem wordMatrix_abs_le {ι δ β : Type*} {p : ℕ} (c : ℤ)
    (l : Combinatorics.Line (δ → Coeff p) ι) (i : WordTarget δ β)
    (j : WordSource ι δ β) : |wordMatrix c l i j| ≤ max (p : ℤ) |c| := by
  unfold wordMatrix
  split_ifs
  · rcases j with ⟨a, t⟩ | v
    · cases ha : l.idxFun a with
      | none =>
          simp only [wordWeight, ha, Option.elim_none]
          exact le_max_right _ _
      | some b =>
          simp only [wordWeight, ha, Option.elim_some]
          exact (show |(b t : ℤ)| ≤ (p : ℤ) from abs_le.mpr (b t).property).trans
            (le_max_left _ _)
    · exact le_max_right _ _
  · exact (by positivity : (0 : ℤ) ≤ (p : ℤ)).trans (le_max_left _ _)

end Sidon.Deuber
