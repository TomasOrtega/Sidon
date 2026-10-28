module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Finite Deuber patterns and disjoint-support generator maps -/

noncomputable section

open scoped BigOperators

namespace Sidon.Deuber

/-- The bounded integer alphabet for the earlier coefficients of a row. -/
abbrev Coeff (p : ℕ) := Set.Icc (-(p : ℤ)) (p : ℤ)

def zeroCoeff (p : ℕ) : Coeff p := ⟨0, by simp⟩

/-- A row has leading coefficient `c` and bounded coefficients at earlier indices. -/
def row {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) (j : ι) : Set ℤ :=
  Set.range fun a : ι → Coeff p =>
    c * z j + ∑ i ∈ Finset.univ.filter (fun i : ι => i < j), (a i : ℤ) * z i

def pattern {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) : Set ℤ :=
  ⋃ j, row p c z j

def IsMonochromatic {κ : Type*} (χ : ℤ → κ) (s : Set ℤ) : Prop :=
  ∃ colour, ∀ x ∈ s, χ x = colour

/-- The final `k` rows are monochromatic, possibly with different colours. -/
def IsRowRegular {n : ℕ} {κ : Type*} (k p : ℕ) (c : ℤ)
    (z : Fin n → ℤ) (χ : ℤ → κ) : Prop :=
  ∀ j : Fin n, n - k ≤ j.val → IsMonochromatic χ (row p c z j)

/-- An invariant description of the final `k` rows of a finite linear order. -/
def IsTailRegular {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    (k p : ℕ) (c : ℤ) (z : ι → ℤ) (χ : ℤ → κ) : Prop :=
  ∀ j : ι, Fintype.card {i : ι // j < i} < k → IsMonochromatic χ (row p c z j)

theorem row_finite {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) (j : ι) :
    (row p c z j).Finite := Set.finite_range _

theorem pattern_finite {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) :
    (pattern p c z).Finite := by
  exact Set.finite_iUnion fun j => row_finite p c z j

theorem row_subset_pattern {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) (j : ι) : row p c z j ⊆ pattern p c z :=
  Set.subset_iUnion (row p c z) j

theorem leading_mem_row {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) (j : ι) : c * z j ∈ row p c z j := by
  refine ⟨fun _ => zeroCoeff p, ?_⟩
  simp [zeroCoeff]

theorem generators_pos_of_pattern_pos {n : ℕ} {p : ℕ} {c : ℤ}
    {z : Fin n → ℤ} (hc : 0 < c) (hpos : ∀ x ∈ pattern p c z, 0 < x)
    (j : Fin n) : 0 < z j := by
  have h := hpos _ (row_subset_pattern p c z j (leading_mem_row p c z j))
  exact (mul_pos_iff_of_pos_left hc).mp h

theorem row_zero {n : ℕ} (hn : 0 < n) (p : ℕ) (c : ℤ) (z : Fin n → ℤ) :
    row p c z ⟨0, hn⟩ = {c * z ⟨0, hn⟩} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp [Fin.lt_def]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact leading_mem_row p c z ⟨0, hn⟩

theorem isMonochromatic_singleton {κ : Type*} (χ : ℤ → κ) (x : ℤ) :
    IsMonochromatic χ {x} := by
  exact ⟨χ x, fun y hy => by simpa using congrArg χ (Set.mem_singleton_iff.mp hy)⟩

theorem isRowRegular_zero {n : ℕ} {κ : Type*} (p : ℕ) (c : ℤ)
    (z : Fin n → ℤ) (χ : ℤ → κ) : IsRowRegular 0 p c z χ := by
  intro j hj
  have := j.isLt
  omega

theorem IsMonochromatic.mono {κ : Type*} {χ : ℤ → κ} {s t : Set ℤ}
    (h : IsMonochromatic χ s) (ht : t ⊆ s) : IsMonochromatic χ t := by
  obtain ⟨colour, hcolour⟩ := h
  exact ⟨colour, fun x hx => hcolour x (ht hx)⟩

theorem sum_eq_leading_add_prefix {ι : Type*} [Fintype ι] [LinearOrder ι]
    {c : ℤ} {a z : ι → ℤ} {j : ι} (haj : a j = c)
    (hafter : ∀ i, j < i → a i = 0) :
    (∑ i, a i * z i) = c * z j +
      ∑ i ∈ Finset.univ.filter (fun i : ι => i < j), a i * z i := by
  classical
  calc
    (∑ i, a i * z i) = ∑ i,
        ((if i = j then c * z j else 0) + (if i < j then a i * z i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_lt h]
      · subst i
        simp [haj]
      · simp [not_lt_of_ge h.le, ne_of_gt h, hafter i h]
    _ = c * z j + ∑ i ∈ Finset.univ.filter (fun i : ι => i < j), a i * z i := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_filter]

theorem sum_mem_row_of_coefficients {ι : Type*} [Fintype ι] [LinearOrder ι]
    {p : ℕ} {c : ℤ} {a z : ι → ℤ} {j : ι} (haj : a j = c)
    (hbefore : ∀ i, i < j → -(p : ℤ) ≤ a i ∧ a i ≤ (p : ℤ))
    (hafter : ∀ i, j < i → a i = 0) :
    (∑ i, a i * z i) ∈ row p c z j := by
  classical
  let b : ι → Coeff p := fun i => if hi : i < j then ⟨a i, hbefore i hi⟩ else zeroCoeff p
  refine ⟨b, ?_⟩
  rw [sum_eq_leading_add_prefix haj hafter]
  change c * z j + (∑ i ∈ Finset.univ.filter (fun i : ι => i < j), (b i : ℤ) * z i) = _
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [b, (Finset.mem_filter.mp hi).2]

theorem mem_row_iff_coefficients {ι : Type*} [Fintype ι] [LinearOrder ι]
    {p : ℕ} {c x : ℤ} {z : ι → ℤ} {j : ι} :
    x ∈ row p c z j ↔ ∃ a : ι → ℤ, a j = c ∧
      (∀ i, i < j → -(p : ℤ) ≤ a i ∧ a i ≤ (p : ℤ)) ∧
      (∀ i, j < i → a i = 0) ∧ x = ∑ i, a i * z i := by
  classical
  constructor
  · rintro ⟨b, rfl⟩
    let a : ι → ℤ := fun i => if i < j then (b i : ℤ) else if i = j then c else 0
    have haj : a j = c := by simp [a]
    have hbefore : ∀ i, i < j → -(p : ℤ) ≤ a i ∧ a i ≤ (p : ℤ) := by
      intro i hi
      dsimp only [a]
      rw [if_pos hi]
      exact (b i).property
    have hafter : ∀ i, j < i → a i = 0 := by
      intro i hi
      simp [a, not_lt_of_ge hi.le, ne_of_gt hi]
    refine ⟨a, haj, hbefore, hafter, ?_⟩
    rw [sum_eq_leading_add_prefix haj hafter]
    change c * z j + (∑ i ∈ Finset.univ.filter (fun i : ι => i < j), (b i : ℤ) * z i) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [a, (Finset.mem_filter.mp hi).2]
  · rintro ⟨a, haj, hbefore, hafter, rfl⟩
    exact sum_mem_row_of_coefficients haj hbefore hafter

theorem row_comp_orderIso_subset {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ)
    (p : ℕ) (c : ℤ) (z : κ → ℤ) (j : ι) :
    row p c (z ∘ e) j ⊆ row p c z (e j) := by
  intro x hx
  obtain ⟨a, haj, hbefore, hafter, hx⟩ := mem_row_iff_coefficients.mp hx
  apply mem_row_iff_coefficients.mpr
  refine ⟨fun k => a (e.symm k), by simpa using haj, ?_, ?_, ?_⟩
  · intro k hk
    apply hbefore
    exact e.lt_iff_lt.mp (by simpa using hk)
  · intro k hk
    apply hafter
    exact e.lt_iff_lt.mp (by simpa using hk)
  · rw [hx]
    apply Fintype.sum_equiv e.toEquiv
    intro i
    simp

theorem row_comp_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ)
    (p : ℕ) (c : ℤ) (z : κ → ℤ) (j : ι) :
    row p c (z ∘ e) j = row p c z (e j) := by
  apply Set.Subset.antisymm (row_comp_orderIso_subset e p c z j)
  have h := row_comp_orderIso_subset e.symm p c (z ∘ e) (e j)
  have hz : (z ∘ e) ∘ e.symm = z := by
    funext k
    exact congrArg z (e.apply_symm_apply k)
  rw [hz, OrderIso.symm_apply_apply] at h
  exact h

theorem pattern_comp_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ)
    (p : ℕ) (c : ℤ) (z : κ → ℤ) :
    pattern p c (z ∘ e) = pattern p c z := by
  ext x
  simp only [pattern, Set.mem_iUnion, row_comp_orderIso]
  exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩,
    fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩

theorem card_above_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ) (j : ι) :
    Fintype.card {i : ι // j < i} = Fintype.card {k : κ // e j < k} := by
  classical
  exact Fintype.card_congr (e.toEquiv.subtypeEquiv fun _ => e.lt_iff_lt.symm)

theorem isTailRegular_comp_orderIso {ι κ η : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ)
    (k p : ℕ) (c : ℤ) (z : κ → ℤ) (χ : ℤ → η) :
    IsTailRegular k p c (z ∘ e) χ ↔ IsTailRegular k p c z χ := by
  constructor
  · intro h j hj
    have hj' : Fintype.card {i : ι // e.symm j < i} < k := by
      rw [card_above_orderIso e]
      simpa using hj
    have hm := h (e.symm j) hj'
    rw [row_comp_orderIso] at hm
    simpa using hm
  · intro h j hj
    rw [card_above_orderIso e] at hj
    rw [row_comp_orderIso]
    exact h (e j) hj

theorem isTailRegular_zero {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℕ) (c : ℤ) (z : ι → ℤ) (χ : ℤ → κ) : IsTailRegular 0 p c z χ := by
  intro j hj
  exact False.elim (Nat.not_lt_zero _ hj)

theorem IsTailRegular.all_rows {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    {p : ℕ} {c : ℤ} {z : ι → ℤ} {χ : ℤ → κ}
    (h : IsTailRegular (Fintype.card ι) p c z χ) :
    ∀ j, IsMonochromatic χ (row p c z j) := by
  intro j
  exact h j (Fintype.card_subtype_lt (lt_irrefl j))

end Sidon.Deuber

namespace Sidon

/-- Every row is nonzero, and distinct rows use disjoint source coordinates. -/
def IsBlockEmbedding {ι κ : Type*} (T : Matrix ι κ ℤ) : Prop :=
  (∀ i, ∃ j, T i j ≠ 0) ∧
    ∀ i i' j, i ≠ i' → T i j = 0 ∨ T i' j = 0

theorem isBlockEmbedding_one {ι : Type*} [DecidableEq ι] :
    IsBlockEmbedding (1 : Matrix ι ι ℤ) := by
  refine ⟨fun i => ⟨i, by simp⟩, ?_⟩
  intro i i' j hii'
  by_cases hij : i = j
  · subst j
    exact Or.inr (by simp [hii'.symm])
  · exact Or.inl (by simp [hij])

theorem IsBlockEmbedding.nonzero_column_unique {ι κ : Type*} {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) {i i' : ι} {j : κ}
    (hi : T i j ≠ 0) (hi' : T i' j ≠ 0) : i = i' := by
  by_contra h
  exact (hT.2 i i' j h).elim hi hi'

theorem IsBlockEmbedding.selectRows {ι ι' κ : Type*} {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (e : ι' ↪ ι) :
    IsBlockEmbedding (fun i j => T (e i) j) := by
  refine ⟨fun i => hT.1 (e i), ?_⟩
  intro i i' j hii'
  exact hT.2 (e i) (e i') j (e.injective.ne hii')

theorem IsBlockEmbedding.submatrix_equiv {ι ι' κ κ' : Type*} {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (e : ι' ≃ ι) (e' : κ' ≃ κ) :
    IsBlockEmbedding (T.submatrix e e') := by
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hT.1 (e i)
    exact ⟨e'.symm j, by simpa [Matrix.submatrix] using hj⟩
  · intro i i' j hii'
    exact hT.2 (e i) (e i') (e' j) (e.injective.ne hii')

theorem IsBlockEmbedding.exists_pivots {ι κ : Type*} {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) : ∃ e : ι ↪ κ, ∀ i, T i (e i) ≠ 0 := by
  classical
  choose e he using hT.1
  refine ⟨⟨e, ?_⟩, he⟩
  intro i i' hii'
  exact hT.nonzero_column_unique (he i) (hii' ▸ he i')

theorem IsBlockEmbedding.card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {T : Matrix ι κ ℤ} (hT : IsBlockEmbedding T) : Fintype.card ι ≤ Fintype.card κ := by
  obtain ⟨e, _⟩ := hT.exists_pivots
  exact Fintype.card_le_of_injective e e.injective

theorem IsBlockEmbedding.mul_apply_of_ne_zero {ι κ ν : Type*} [Fintype κ]
    {T : Matrix ι κ ℤ} {U : Matrix κ ν ℤ} (hU : IsBlockEmbedding U)
    (i : ι) {j : κ} {k : ν} (hjk : U j k ≠ 0) :
    (T * U) i k = T i j * U j k := by
  classical
  rw [Matrix.mul_apply]
  apply Fintype.sum_eq_single j
  intro j' hne
  have hj' : U j' k = 0 := (hU.2 j' j k hne).resolve_right hjk
  simp [hj']

theorem IsBlockEmbedding.vecMul_apply_of_ne_zero {ι κ : Type*} [Fintype ι]
    {T : Matrix ι κ ℤ} (hT : IsBlockEmbedding T) (w : ι → ℤ)
    {i : ι} {j : κ} (hij : T i j ≠ 0) :
    Matrix.vecMul w T j = w i * T i j := by
  classical
  rw [Matrix.vecMul, dotProduct]
  apply Fintype.sum_eq_single i
  intro i' hne
  have hi' : T i' j = 0 := (hT.2 i' i j hne).resolve_right hij
  simp [hi']

theorem IsBlockEmbedding.mul {ι κ ν : Type*} [Fintype κ]
    {T : Matrix ι κ ℤ} {U : Matrix κ ν ℤ}
    (hT : IsBlockEmbedding T) (hU : IsBlockEmbedding U) :
    IsBlockEmbedding (T * U) := by
  classical
  constructor
  · intro i
    obtain ⟨j, hj⟩ := hT.1 i
    obtain ⟨k, hk⟩ := hU.1 j
    exact ⟨k, by rw [hU.mul_apply_of_ne_zero i hk]; exact mul_ne_zero hj hk⟩
  · intro i i' k hii'
    by_cases hk : ∃ j, U j k ≠ 0
    · obtain ⟨j, hj⟩ := hk
      rw [hU.mul_apply_of_ne_zero i hj, hU.mul_apply_of_ne_zero i' hj]
      rcases hT.2 i i' j hii' with hi | hi'
      · exact Or.inl (by rw [hi, zero_mul])
      · exact Or.inr (by rw [hi', zero_mul])
    · push_neg at hk
      exact Or.inl (by simp [Matrix.mul_apply, hk])

end Sidon
