module

public import Sidon.Combinatorics.Deuber.OrderedExtraction
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Reindexing and iterating finite Deuber extraction -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.Deuber

local instance finSourceOrder (h d k : ℕ) :
    LinearOrder (WordSource (Fin h) (Fin d) (Fin k)) :=
  wordSourceOrder _ _ _

local instance finTargetOrder (d k : ℕ) : LinearOrder (WordTarget (Fin d) (Fin k)) :=
  wordTargetOrder _ _

local instance finSourceLE (h d k : ℕ) : LE (WordSource (Fin h) (Fin d) (Fin k)) :=
  (wordSourceOrder (Fin h) (Fin d) (Fin k)).toLE

local instance finTargetLE (d k : ℕ) : LE (WordTarget (Fin d) (Fin k)) :=
  (wordTargetOrder (Fin d) (Fin k)).toLE

theorem exists_fin_extraction_step {n k : ℕ} (hkn : k < n)
    (p c r : ℕ) (hc : 0 < c) (hr : 0 < r) :
    ∃ N : ℕ, n ≤ N ∧ ∃ family : Set (Matrix (Fin n) (Fin N) ℤ),
      family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
      ∀ (Y : Fin N → ℤ) (χ : ℤ → Fin r),
        IsTailRegular k (max p c * max p c) ((c : ℤ) * (c : ℤ)) Y χ →
        ∃ T ∈ family,
          pattern p (c : ℤ) (T.mulVec Y) ⊆
            pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) Y ∧
          IsTailRegular (k + 1) p (c : ℤ) (T.mulVec Y) χ := by
  let d := n - k - 1
  have hdn : d + k + 1 = n := by dsimp [d]; omega
  obtain ⟨h, hpos, family, hfinite, hblock, hextract⟩ :=
    exists_tail_extraction_step (δ := Fin d) (β := Fin k) p c r hc hr
  let N := h * d + k + 1
  have hnN : n ≤ N := by
    have hmul : d ≤ h * d := by
      simpa using Nat.mul_le_mul_right d (Nat.succ_le_of_lt hpos)
    dsimp [N]
    omega
  let et : Fin n ≃o WordTarget (Fin d) (Fin k) :=
    Fintype.orderIsoFinOfCardEq _ (by simp [WordTarget]; omega)
  let es : Fin N ≃o WordSource (Fin h) (Fin d) (Fin k) :=
    Fintype.orderIsoFinOfCardEq _ (by simp [WordSource, N, Nat.add_assoc])
  let reindex := fun T : Matrix (WordTarget (Fin d) (Fin k))
      (WordSource (Fin h) (Fin d) (Fin k)) ℤ => T.submatrix et es
  refine ⟨N, hnN, reindex '' family, hfinite.image reindex, ?_, ?_⟩
  · rintro T ⟨U, hU, rfl⟩
    exact (hblock U hU).submatrix_equiv et.toEquiv es.toEquiv
  · intro Y χ hreg
    let S := Y ∘ es.symm
    have hS : S ∘ es = Y := by
      funext i
      simp [S]
    have hregS : IsTailRegular (Fintype.card (Fin k)) (max p c * max p c)
        ((c : ℤ) * (c : ℤ)) S χ := by
      apply (isTailRegular_comp_orderIso es _ _ _ S χ).mp
      simpa only [hS, Fintype.card_fin] using hreg
    obtain ⟨T, hT, hsub, hregT⟩ := hextract S χ hregS
    have hZ : (reindex T).mulVec Y = (T.mulVec S) ∘ et :=
      Matrix.submatrix_mulVec_equiv T Y et es.toEquiv
    refine ⟨reindex T, ⟨T, hT, rfl⟩, ?_, ?_⟩
    · rw [hZ, pattern_comp_orderIso et]
      have hsource : pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) S =
          pattern (max p c * max p c) ((c : ℤ) * (c : ℤ)) Y := by
        have heq := pattern_comp_orderIso es (max p c * max p c)
          ((c : ℤ) * (c : ℤ)) S
        rw [hS] at heq
        exact heq.symm
      exact hsource ▸ hsub
    · rw [hZ]
      apply (isTailRegular_comp_orderIso et _ _ _ (T.mulVec S) χ).mpr
      simpa only [Fintype.card_fin] using hregT

theorem exists_tail_extraction (k n p c r : ℕ) (hkn : k ≤ n)
    (hp : 0 < p) (hc : 0 < c) (hr : 0 < r) :
    ∃ N : ℕ, n ≤ N ∧ ∃ P C : ℕ, 0 < P ∧ 0 < C ∧
      ∃ family : Set (Matrix (Fin n) (Fin N) ℤ),
        family.Finite ∧ (∀ T ∈ family, IsBlockEmbedding T) ∧
        ∀ (Y : Fin N → ℤ) (χ : ℤ → Fin r), ∃ T ∈ family,
          pattern p (c : ℤ) (T.mulVec Y) ⊆ pattern P (C : ℤ) Y ∧
          IsTailRegular k p (c : ℤ) (T.mulVec Y) χ := by
  induction k generalizing n p c with
  | zero =>
      refine ⟨n, le_rfl, p, c, hp, hc, {(1 : Matrix (Fin n) (Fin n) ℤ)},
        Set.finite_singleton _, ?_, ?_⟩
      · intro T hT
        have hT' : T = 1 := Set.mem_singleton_iff.mp hT
        rw [hT']
        exact isBlockEmbedding_one
      · intro Y χ
        refine ⟨1, Set.mem_singleton _, ?_, ?_⟩
        · simp
        · exact isTailRegular_zero p (c : ℤ) _ χ
  | succ k ih =>
      obtain ⟨N₀, hnN₀, family₀, hfinite₀, hblock₀, hstep⟩ :=
        exists_fin_extraction_step (n := n) (k := k) (by omega) p c r hc hr
      let P₀ := max p c * max p c
      let C₀ := c * c
      have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
      have hC₀ : 0 < C₀ := Nat.mul_pos hc hc
      obtain ⟨N₁, hN₀N₁, P₁, C₁, hP₁, hC₁, family₁, hfinite₁, hblock₁, hextract₁⟩ :=
        ih N₀ P₀ C₀ (by omega) hP₀ hC₀
      let family := Set.image2 (fun T U => T * U) family₀ family₁
      refine ⟨N₁, hnN₀.trans hN₀N₁, P₁, C₁, hP₁, hC₁, family,
        hfinite₀.image2 (fun T U => T * U) hfinite₁, ?_, ?_⟩
      · rintro V ⟨T, hT, U, hU, rfl⟩
        exact (hblock₀ T hT).mul (hblock₁ U hU)
      · intro Y χ
        obtain ⟨U, hU, hsubU, hregU⟩ := hextract₁ Y χ
        have hregU' : IsTailRegular k (max p c * max p c)
            ((c : ℤ) * (c : ℤ)) (U.mulVec Y) χ := by
          simpa only [P₀, C₀, Nat.cast_mul] using hregU
        obtain ⟨T, hT, hsubT, hregT⟩ := hstep (U.mulVec Y) χ hregU'
        have hmul : (T * U).mulVec Y = T.mulVec (U.mulVec Y) :=
          (Matrix.mulVec_mulVec Y T U).symm
        refine ⟨T * U, ⟨T, hT, U, hU, rfl⟩, ?_, ?_⟩
        · rw [hmul]
          apply Set.Subset.trans _ hsubU
          simpa only [P₀, C₀, Nat.cast_mul] using hsubT
        · rw [hmul]
          exact hregT

end Sidon.Deuber
