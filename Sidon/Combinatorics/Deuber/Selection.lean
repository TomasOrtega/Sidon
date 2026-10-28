module

public import Sidon.Combinatorics.Deuber.Iteration
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section

/-! # Selecting a monochromatic subpattern -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.Deuber

theorem row_mono {ι : Type*} [Fintype ι] [LinearOrder ι]
    {p P : ℕ} (hp : p ≤ P) (c : ℤ) (z : ι → ℤ) (j : ι) :
    row p c z j ⊆ row P c z j := by
  intro x hx
  obtain ⟨a, haj, hbefore, hafter, rfl⟩ := mem_row_iff_coefficients.mp hx
  apply sum_mem_row_of_coefficients haj _ hafter
  intro i hi
  have hp' : (p : ℤ) ≤ (P : ℤ) := by exact_mod_cast hp
  obtain ⟨hl, hu⟩ := hbefore i hi
  constructor <;> linarith

theorem pattern_mono {ι : Type*} [Fintype ι] [LinearOrder ι]
    {p P : ℕ} (hp : p ≤ P) (c : ℤ) (z : ι → ℤ) :
    pattern p c z ⊆ pattern P c z := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact row_subset_pattern _ _ _ j (row_mono hp c z j hj)

def selectionMatrix {ι κ : Type*} [Preorder ι] [Preorder κ]
    (e : ι ↪o κ) : Matrix ι κ ℤ := fun i j => if e i = j then 1 else 0

theorem selectionMatrix_isBlockEmbedding {ι κ : Type*} [Preorder ι] [Preorder κ]
    (e : ι ↪o κ) : IsBlockEmbedding (selectionMatrix e) := by
  constructor
  · intro i
    exact ⟨e i, by simp [selectionMatrix]⟩
  · intro i i' j hii'
    by_cases h : e i = j
    · right
      have h' : e i' ≠ j := by
        intro h'
        exact hii' (e.injective (h.trans h'.symm))
      simp [selectionMatrix, h']
    · left
      simp [selectionMatrix, h]

theorem selectionMatrix_isLeadingEmbedding {ι κ : Type*}
    [Preorder ι] [Preorder κ] (e : ι ↪o κ) :
    IsLeadingEmbedding (selectionMatrix e) e 1 := by
  refine ⟨selectionMatrix_isBlockEmbedding e, fun i => ⟨?_, ?_⟩⟩
  · simp [selectionMatrix]
  · intro j hj
    simp [selectionMatrix, ne_of_lt hj]

theorem selectionMatrix_mulVec {ι κ : Type*} [Fintype κ]
    [Preorder ι] [Preorder κ] (e : ι ↪o κ) (z : κ → ℤ) :
    (selectionMatrix e).mulVec z = z ∘ e := by
  funext i
  simp [Matrix.mulVec, dotProduct, selectionMatrix]

theorem row_comp_orderEmbedding_subset {ι κ : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ↪o κ) (p : ℕ) (c : ℤ) (hc : |c| ≤ (p : ℤ)) (z : κ → ℤ) (j : ι) :
    row p c (z ∘ e) j ⊆ row p c z (e j) := by
  have hbound : ∀ i k, |selectionMatrix e i k| ≤ (1 : ℤ) := by
    intro i k
    simp only [selectionMatrix]
    split_ifs <;> norm_num
  have h := (selectionMatrix_isLeadingEmbedding e).row_subset_mul
    (by norm_num) (le_refl p) hc hbound z j
  simpa only [selectionMatrix_mulVec, Nat.mul_one, mul_one] using h

theorem pattern_comp_orderEmbedding_subset {ι κ : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ↪o κ) (p : ℕ) (c : ℤ) (hc : |c| ≤ (p : ℤ)) (z : κ → ℤ) :
    pattern p c (z ∘ e) ⊆ pattern p c z := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact row_subset_pattern _ _ _ (e j) (row_comp_orderEmbedding_subset e p c hc z j hj)

theorem exists_mono_row_selection {q n r : ℕ} (hq : 0 < q)
    (hn : r * (q - 1) < n) (p : ℕ) (c : ℤ) (hc : |c| ≤ (p : ℤ))
    (z : Fin n → ℤ) (χ : ℤ → Fin r)
    (hrows : ∀ j, IsMonochromatic χ (row p c z j)) :
    ∃ e : Fin q ↪o Fin n, IsMonochromatic χ (pattern p c (z ∘ e)) := by
  let f : Fin n → Fin r := fun j => χ (c * z j)
  obtain ⟨colour, hcolour⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := f) (n := q - 1) (by simpa using hn)
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (by omega :
    q ≤ (Finset.univ.filter (fun j => f j = colour)).card)
  let e := s.orderEmbOfFin hcard
  refine ⟨e, colour, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have hjmem : e j ∈ s := s.orderEmbOfFin_mem hcard j
  have heq : χ (c * z (e j)) = colour := (Finset.mem_filter.mp (hs hjmem)).2
  obtain ⟨colour', hcolour'⟩ := hrows (e j)
  have hlead := hcolour' _ (leading_mem_row p c z (e j))
  have hx' := row_comp_orderEmbedding_subset e p c hc z j hj
  exact (hcolour' x hx').trans (hlead.symm.trans heq)

theorem exists_finite_extraction (q p c r : ℕ) (hq : 0 < q)
    (hp : 0 < p) (hc : 0 < c) (hr : 0 < r) :
    ∃ N : ℕ, q ≤ N ∧ ∃ P C : ℕ, 0 < P ∧ 0 < C ∧
      ∃ family : Set (Matrix (Fin q) (Fin N) ℤ),
        family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
        ∀ (Y : Fin N → ℤ) (χ : ℤ → Fin r), ∃ T ∈ family,
          pattern p (c : ℤ) (T.mulVec Y) ⊆ pattern P (C : ℤ) Y ∧
          IsMonochromatic χ (pattern p (c : ℤ) (T.mulVec Y)) := by
  let n := r * (q - 1) + 1
  have hqn : q ≤ n := by
    have hmul := Nat.mul_le_mul_right (q - 1) (Nat.succ_le_of_lt hr)
    dsimp [n]
    omega
  obtain ⟨N, hnN, P, C, hP, hC, family, hfinite, hblock, hextract⟩ :=
    exists_tail_extraction n n (max p c) c r (le_refl n) (by positivity) hc hr
  letI : Finite (Fin q ↪o Fin n) :=
    Finite.of_injective (fun e : Fin q ↪o Fin n => (fun i => e i))
      (fun e e' h => DFunLike.ext' h)
  let selections : Set (Matrix (Fin q) (Fin n) ℤ) := Set.range selectionMatrix
  have hselections : selections.Finite := Set.finite_range _
  let combined := Set.image2 (fun V T => V * T) selections family
  refine ⟨N, hqn.trans hnN, P, C, hP, hC, combined,
    hselections.image2 (fun V T => V * T) hfinite, ?_, ?_⟩
  · rintro U ⟨V, ⟨e, rfl⟩, T, hT, rfl⟩
    exact (selectionMatrix_isBlockEmbedding e).mul (hblock T hT)
  · intro Y χ
    obtain ⟨T, hT, hsub, hreg⟩ := hextract Y χ
    have hcmax : |(c : ℤ)| ≤ ((max p c : ℕ) : ℤ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg c)]
      exact_mod_cast le_max_right p c
    have hrows : ∀ j, IsMonochromatic χ (row (max p c) (c : ℤ) (T.mulVec Y) j) := by
      apply IsTailRegular.all_rows
      simpa only [Fintype.card_fin] using hreg
    obtain ⟨e, he⟩ := exists_mono_row_selection hq (by dsimp [n]; omega)
      (max p c) (c : ℤ) hcmax (T.mulVec Y) χ hrows
    have hmul : (selectionMatrix e * T).mulVec Y = (T.mulVec Y) ∘ e := by
      rw [← Matrix.mulVec_mulVec, selectionMatrix_mulVec]
    refine ⟨selectionMatrix e * T, ⟨selectionMatrix e, ⟨e, rfl⟩, T, hT, rfl⟩,
      ?_, ?_⟩
    · rw [hmul]
      exact (pattern_mono (le_max_left p c) _ _).trans
        ((pattern_comp_orderEmbedding_subset e (max p c) (c : ℤ) hcmax _).trans hsub)
    · rw [hmul]
      exact he.mono (pattern_mono (le_max_left p c) _ _)

end Sidon.Deuber
