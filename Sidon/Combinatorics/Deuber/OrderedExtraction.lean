import Sidon.Combinatorics.Deuber.Extraction

/-! # Ordered row containment for the Hales--Jewett block maps -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.Deuber

def wordSourceOrderEquiv (ι δ β : Type*) :
    WordSource ι δ β ≃ ((Lex (ι × δ)) ⊕ₗ WithBot β) :=
  (Equiv.sumCongr toLex (Equiv.refl _)).trans toLex

def wordTargetOrderEquiv (δ β : Type*) : WordTarget δ β ≃ (δ ⊕ₗ WithBot β) :=
  toLex

def wordSourceOrder (ι δ β : Type*) [LinearOrder ι] [LinearOrder δ] [LinearOrder β] :
    LinearOrder (WordSource ι δ β) :=
  LinearOrder.lift' (wordSourceOrderEquiv ι δ β) (wordSourceOrderEquiv ι δ β).injective

def wordTargetOrder (δ β : Type*) [LinearOrder δ] [LinearOrder β] :
    LinearOrder (WordTarget δ β) :=
  LinearOrder.lift' (wordTargetOrderEquiv δ β) (wordTargetOrderEquiv δ β).injective

section Ordered

variable {ι δ β : Type*} [LinearOrder ι] [LinearOrder δ] [LinearOrder β]

local instance sourceOrder : LinearOrder (WordSource ι δ β) := wordSourceOrder ι δ β
local instance targetOrder : LinearOrder (WordTarget δ β) := wordTargetOrder δ β
local instance sourceLE : LE (WordSource ι δ β) := (wordSourceOrder ι δ β).toLE
local instance sourceLT : LT (WordSource ι δ β) := (wordSourceOrder ι δ β).toLT
local instance targetLE : LE (WordTarget δ β) := (wordTargetOrder δ β).toLE
local instance targetLT : LT (WordTarget δ β) := (wordTargetOrder δ β).toLT

theorem wordSource_prefix_le_prefix (i j : ι) (t u : δ) :
    (Sum.inl (i, t) : WordSource ι δ β) ≤ Sum.inl (j, u) ↔
      i < j ∨ i = j ∧ t ≤ u := by
  change (toLex (Sum.inl (toLex (i, t))) : (Lex (ι × δ)) ⊕ₗ WithBot β) ≤
    toLex (Sum.inl (toLex (j, u))) ↔ _
  rw [Sum.Lex.inl_le_inl_iff, Prod.Lex.le_iff]

theorem wordSource_prefix_lt_extra (i : ι) (t : δ) (v : Option β) :
    (Sum.inl (i, t) : WordSource ι δ β) < Sum.inr v := by
  change (toLex (Sum.inl (toLex (i, t))) : (Lex (ι × δ)) ⊕ₗ WithBot β) <
    toLex (Sum.inr v)
  exact Sum.Lex.inl_lt_inr _ _

theorem wordSource_not_extra_lt_prefix (v : Option β) (i : ι) (t : δ) :
    ¬(Sum.inr v : WordSource ι δ β) < Sum.inl (i, t) := by
  change ¬(toLex (Sum.inr v) : (Lex (ι × δ)) ⊕ₗ WithBot β) <
    toLex (Sum.inl (toLex (i, t)))
  exact Sum.Lex.not_inr_lt_inl

theorem wordSource_not_extra_lt_middle (v : Option β) :
    ¬(Sum.inr v : WordSource ι δ β) < Sum.inr none := by
  change ¬(toLex (Sum.inr v) : (Lex (ι × δ)) ⊕ₗ WithBot β) < toLex (Sum.inr none)
  intro h
  exact (WithBot.not_lt_bot (α := β) v)
    ((Sum.Lex.inr_lt_inr_iff (α := Lex (ι × δ)) (β := WithBot β)).mp h)

theorem wordSource_late_lt_late (v w : β) :
    (Sum.inr (some v) : WordSource ι δ β) < Sum.inr (some w) ↔ v < w := by
  change (toLex (Sum.inr (some v)) : (Lex (ι × δ)) ⊕ₗ WithBot β) <
    toLex (Sum.inr (some w)) ↔ _
  exact (Sum.Lex.inr_lt_inr_iff (α := Lex (ι × δ)) (β := WithBot β)).trans
    WithBot.coe_lt_coe

theorem wordTarget_early_lt_extra (t : δ) (v : Option β) :
    (Sum.inl t : WordTarget δ β) < Sum.inr v := by
  change (toLex (Sum.inl t) : δ ⊕ₗ WithBot β) < toLex (Sum.inr v)
  exact Sum.Lex.inl_lt_inr _ _

theorem wordTarget_early_lt_middle (t : δ) :
    (Sum.inl t : WordTarget δ β) < Sum.inr none := by
  change (toLex (Sum.inl t) : δ ⊕ₗ WithBot β) < toLex (Sum.inr none)
  exact Sum.Lex.inl_lt_inr _ _

theorem wordTarget_not_extra_lt_middle (v : Option β) :
    ¬(Sum.inr v : WordTarget δ β) < Sum.inr none := by
  change ¬(toLex (Sum.inr v) : δ ⊕ₗ WithBot β) < toLex (Sum.inr none)
  intro h
  exact (WithBot.not_lt_bot (α := β) v)
    ((Sum.Lex.inr_lt_inr_iff (α := δ) (β := WithBot β)).mp h)

theorem card_wordSource_above_late_lt [Fintype ι] [Fintype δ] [Fintype β] (v : β) :
    Fintype.card {j : WordSource ι δ β // Sum.inr (some v) < j} < Fintype.card β := by
  let f : {w : β // v < w} → {j : WordSource ι δ β // Sum.inr (some v) < j} :=
    fun w => ⟨Sum.inr (some w.val), (wordSource_late_lt_late v w.val).mpr w.property⟩
  have hinj : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    simpa [f] using h'
  have hsurj : Function.Surjective f := by
    rintro ⟨j, hj⟩
    rcases j with ⟨i, t⟩ | w
    · exact False.elim (wordSource_not_extra_lt_prefix (some v) i t hj)
    · cases w with
      | none => exact False.elim (wordSource_not_extra_lt_middle (some v) hj)
      | some w => exact ⟨⟨w, (wordSource_late_lt_late v w).mp hj⟩, rfl⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [← hcard]
  exact Fintype.card_subtype_lt (lt_irrefl v)

omit [LinearOrder ι] in
theorem card_wordTarget_above_early_ge [Fintype δ] [Fintype β] (t : δ) :
    Fintype.card β + 1 ≤ Fintype.card {j : WordTarget δ β // Sum.inl t < j} := by
  let f : Option β → {j : WordTarget δ β // Sum.inl t < j} :=
    fun v => ⟨Sum.inr v, wordTarget_early_lt_extra t v⟩
  have hinj : Function.Injective f := by
    intro v v' h
    have h' := congrArg Subtype.val h
    simpa [f] using h'
  simpa using Fintype.card_le_of_injective f hinj

omit [LinearOrder ι] in
theorem isTailRegular_of_middle_late [Fintype δ] [Fintype β]
    {κ : Type*} {p : ℕ} {c : ℤ} {z : WordTarget δ β → ℤ} {χ : ℤ → κ}
    (hmiddle : IsMonochromatic χ (row p c z (Sum.inr none)))
    (hlate : ∀ v : β, IsMonochromatic χ (row p c z (Sum.inr (some v)))) :
    IsTailRegular (Fintype.card β + 1) p c z χ := by
  intro j hj
  rcases j with t | v
  · have hbound := card_wordTarget_above_early_ge (β := β) t
    omega
  · cases v with
    | none => exact hmiddle
    | some v => exact hlate v

def wordLeader (a : ι) : WordTarget δ β ↪o WordSource ι δ β where
  toFun
    | Sum.inl t => Sum.inl (a, t)
    | Sum.inr v => Sum.inr v
  inj' := by
    intro i j hij
    cases i <;> cases j <;> simp_all
  map_rel_iff' := by
    intro i j
    rcases i with t | v <;> rcases j with u | v'
    · change (toLex (Sum.inl (toLex (a, t))) : (Lex (ι × δ)) ⊕ₗ WithBot β) ≤
        toLex (Sum.inl (toLex (a, u))) ↔
          (toLex (Sum.inl t) : δ ⊕ₗ WithBot β) ≤ toLex (Sum.inl u)
      simp [Sum.Lex.inl_le_inl_iff, Prod.Lex.le_iff]
    · change (toLex (Sum.inl (toLex (a, t))) : (Lex (ι × δ)) ⊕ₗ WithBot β) ≤
        toLex (Sum.inr v') ↔
          (toLex (Sum.inl t) : δ ⊕ₗ WithBot β) ≤ toLex (Sum.inr v')
      exact ⟨fun _ => Sum.Lex.inl_le_inr _ _, fun _ => Sum.Lex.inl_le_inr _ _⟩
    · change (toLex (Sum.inr v) : (Lex (ι × δ)) ⊕ₗ WithBot β) ≤
        toLex (Sum.inl (toLex (a, u))) ↔
          (toLex (Sum.inr v) : δ ⊕ₗ WithBot β) ≤ toLex (Sum.inl u)
      exact ⟨fun h => False.elim (Sum.Lex.not_inr_le_inl h),
        fun h => False.elim (Sum.Lex.not_inr_le_inl h)⟩
    · change (toLex (Sum.inr v) : (Lex (ι × δ)) ⊕ₗ WithBot β) ≤
        toLex (Sum.inr v') ↔
          (toLex (Sum.inr v) : δ ⊕ₗ WithBot β) ≤ toLex (Sum.inr v')
      exact ⟨fun h => Sum.Lex.inr_le_inr_iff.mpr (Sum.Lex.inr_le_inr_iff.mp h),
        fun h => Sum.Lex.inr_le_inr_iff.mpr (Sum.Lex.inr_le_inr_iff.mp h)⟩

@[simp]
theorem wordLeader_early (a : ι) (t : δ) :
    wordLeader (β := β) a (Sum.inl t) = Sum.inl (a, t) := rfl

@[simp]
theorem wordLeader_extra (a : ι) (v : Option β) :
    wordLeader (δ := δ) a (Sum.inr v) = Sum.inr v := rfl

theorem wordMatrix_isLeadingEmbedding {p : ℕ} {c : ℤ}
    (hc : c ≠ 0) (l : Combinatorics.Line (δ → Coeff p) ι) (a : ι)
    (ha : l.idxFun a = none) (hmax : ∀ i, l.idxFun i = none → i ≤ a) :
    IsLeadingEmbedding (wordMatrix (β := β) c l) (wordLeader a) c := by
  refine ⟨wordMatrix_isBlockEmbedding hc l, ?_⟩
  intro i
  constructor
  · rcases i with t | v
    · simp [wordMatrix_early_prefix, ha]
    · simp [wordMatrix_extra]
  · intro j hij
    rcases i with t | v <;> rcases j with ⟨b, u⟩ | v'
    · by_cases hb : l.idxFun b = none
      · by_cases htu : t = u
        · subst u
          have hle : (Sum.inl (b, t) : WordSource ι δ β) ≤ Sum.inl (a, t) := by
            apply (wordSource_prefix_le_prefix b a t t).mpr
            exact (lt_or_eq_of_le (hmax b hb)).imp id (fun h => ⟨h, le_rfl⟩)
          exact False.elim ((not_lt_of_ge hle) hij)
        · simp [wordMatrix_early_prefix, htu]
      · simp [wordMatrix_early_prefix, hb]
    · exact wordMatrix_early_extra c l t v'
    · exact False.elim ((not_lt_of_ge (wordSource_prefix_lt_extra b u v).le) hij)
    · by_cases hv : v = v'
      · subst v'
        exact False.elim (lt_irrefl (Sum.inr v : WordSource ι δ β) hij)
      · simp [wordMatrix_extra, hv]

omit [LinearOrder δ] [LinearOrder β] in
theorem exists_max_variable [Fintype ι] {p : ℕ}
    (l : Combinatorics.Line (δ → Coeff p) ι) :
    ∃ a, l.idxFun a = none ∧ ∀ i, l.idxFun i = none → i ≤ a := by
  let A := Finset.univ.filter fun i => l.idxFun i = none
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨A.max' hA, (Finset.mem_filter.mp (Finset.max'_mem A hA)).2, ?_⟩
  intro i hi
  exact Finset.le_max' A i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

theorem wordMatrix_row_subset [Fintype ι] [Fintype δ] [Fintype β]
    {p c : ℕ} (hc : 0 < c) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) :
    ∃ a : ι, ∀ j : WordTarget δ β,
      row p (c : ℤ) ((wordMatrix (c : ℤ) l).mulVec S) j ⊆
        row (max p c * max p c) ((c : ℤ) * (c : ℤ)) S (wordLeader a j) := by
  obtain ⟨a, ha, hmax⟩ := exists_max_variable l
  refine ⟨a, ?_⟩
  intro j
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  apply (wordMatrix_isLeadingEmbedding hc' l a ha hmax).row_subset hc' (le_max_left p c)
  · rw [abs_of_nonneg (Int.natCast_nonneg c)]
    exact_mod_cast le_max_right p c
  · intro i k
    simpa only [Nat.cast_max, abs_of_nonneg (Int.natCast_nonneg c)] using
      wordMatrix_abs_le (c : ℤ) l i k

theorem row_middle [Fintype δ] [Fintype β] (p : ℕ) (c : ℤ)
    (z : WordTarget δ β → ℤ) :
    row p c z (Sum.inr none) = Set.range fun a : δ → Coeff p =>
      c * z (Sum.inr none) + ∑ t, (a t : ℤ) * z (Sum.inl t) := by
  have hsum : ∀ a : WordTarget δ β → Coeff p,
      (∑ i ∈ Finset.univ.filter (fun i : WordTarget δ β => i < Sum.inr none),
        (a i : ℤ) * z i) = ∑ t, (a (Sum.inl t) : ℤ) * z (Sum.inl t) := by
    intro a
    simp [Finset.sum_filter, Fintype.sum_sum_type, wordTarget_early_lt_middle,
      wordTarget_not_extra_lt_middle]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun t => a (Sum.inl t), ?_⟩
    dsimp only
    rw [hsum]
  · rintro ⟨a, rfl⟩
    refine ⟨Sum.elim a (fun _ => zeroCoeff p), ?_⟩
    dsimp only
    rw [hsum]
    rfl

omit [LinearOrder ι] in
theorem wordMatrix_middle_isMonochromatic [Fintype ι] [Fintype δ] [Fintype β]
    {κ : Type*} {p : ℕ} (c : ℤ) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) (χ : ℤ → κ)
    (hl : l.IsMono (fun a => χ (wordEvaluation c S a))) :
    IsMonochromatic χ (row p c ((wordMatrix c l).mulVec S) (Sum.inr none)) := by
  obtain ⟨colour, hcolour⟩ := focusedRow_isMonochromatic c l S χ hl
  refine ⟨colour, ?_⟩
  intro x hx
  rw [row_middle] at hx
  obtain ⟨a, rfl⟩ := hx
  exact hcolour a

theorem wordMatrix_pattern_subset [Fintype ι] [Fintype δ] [Fintype β]
    {p c : ℕ} (hc : 0 < c) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) :
    pattern p (c : ℤ) ((wordMatrix (c : ℤ) l).mulVec S) ⊆
      pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) S := by
  obtain ⟨a, hrows⟩ := wordMatrix_row_subset hc l S
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact row_subset_pattern _ _ _ (wordLeader a j) (hrows j hj)

theorem wordMatrix_late_row_subset [Fintype ι] [Fintype δ] [Fintype β]
    {p c : ℕ} (hc : 0 < c) (l : Combinatorics.Line (δ → Coeff p) ι)
    (S : WordSource ι δ β → ℤ) (v : β) :
    row p (c : ℤ) ((wordMatrix (c : ℤ) l).mulVec S) (Sum.inr (some v)) ⊆
      row (max p c * max p c) ((c : ℤ) * (c : ℤ)) S (Sum.inr (some v)) := by
  obtain ⟨a, hrows⟩ := wordMatrix_row_subset hc l S
  exact hrows (Sum.inr (some v))

omit [LinearOrder ι] in
theorem exists_ordered_extraction_step [Fintype δ] [Fintype β]
    (p c r : ℕ) (hc : 0 < c) (hr : 0 < r) :
    ∃ h : ℕ, 0 < h ∧ ∃ family : Set
      (Matrix (WordTarget δ β) (WordSource (Fin h) δ β) ℤ),
      family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
      ∀ (S : WordSource (Fin h) δ β → ℤ) (χ : ℤ → Fin r),
        (∀ v : β, IsMonochromatic χ
          (row (max p c * max p c) ((c : ℤ) * (c : ℤ)) S (Sum.inr (some v)))) →
        ∃ T ∈ family,
          pattern p (c : ℤ) (T.mulVec S) ⊆
            pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) S ∧
          IsMonochromatic χ (row p (c : ℤ) (T.mulVec S) (Sum.inr none)) ∧
          ∀ v : β, IsMonochromatic χ (row p (c : ℤ) (T.mulVec S) (Sum.inr (some v))) := by
  obtain ⟨h, hpos, hh⟩ := exists_fin_wordLength (δ → Coeff p) r hr
  refine ⟨h, hpos,
    Set.range (wordMatrix (ι := Fin h) (δ := δ) (β := β) (p := p) (c : ℤ)),
    wordMatrices_finite p (c : ℤ), ?_, ?_⟩
  · rintro T ⟨l, rfl⟩
    exact wordMatrix_isBlockEmbedding (by exact_mod_cast ne_of_gt hc) l
  · intro S χ hlate
    obtain ⟨l, hl⟩ := hh (fun a => χ (wordEvaluation (c : ℤ) S a))
    refine ⟨wordMatrix (c : ℤ) l, ⟨l, rfl⟩, wordMatrix_pattern_subset hc l S,
      wordMatrix_middle_isMonochromatic (c : ℤ) l S χ hl, ?_⟩
    intro v
    exact (hlate v).mono (wordMatrix_late_row_subset hc l S v)

omit [LinearOrder ι] in
theorem exists_tail_extraction_step [Fintype δ] [Fintype β]
    (p c r : ℕ) (hc : 0 < c) (hr : 0 < r) :
    ∃ h : ℕ, 0 < h ∧ ∃ family : Set
      (Matrix (WordTarget δ β) (WordSource (Fin h) δ β) ℤ),
      family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
      ∀ (S : WordSource (Fin h) δ β → ℤ) (χ : ℤ → Fin r),
        IsTailRegular (Fintype.card β) (max p c * max p c)
          ((c : ℤ) * (c : ℤ)) S χ →
        ∃ T ∈ family,
          pattern p (c : ℤ) (T.mulVec S) ⊆
            pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) S ∧
          IsTailRegular (Fintype.card β + 1) p (c : ℤ) (T.mulVec S) χ := by
  obtain ⟨h, hpos, family, hfinite, hblock, hextract⟩ :=
    exists_ordered_extraction_step (δ := δ) (β := β) p c r hc hr
  refine ⟨h, hpos, family, hfinite, hblock, ?_⟩
  intro S χ hreg
  have hlate : ∀ v : β, IsMonochromatic χ
      (row (max p c * max p c) ((c : ℤ) * (c : ℤ)) S (Sum.inr (some v))) := by
    intro v
    exact hreg (Sum.inr (some v)) (card_wordSource_above_late_lt v)
  obtain ⟨T, hT, hsubset, hmiddle, hlate'⟩ := hextract S χ hlate
  exact ⟨T, hT, hsubset, isTailRegular_of_middle_late hmiddle hlate'⟩

end Ordered

end Sidon.Deuber
