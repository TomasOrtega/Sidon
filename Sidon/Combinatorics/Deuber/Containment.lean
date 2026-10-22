import Sidon.Combinatorics.Deuber.Basic

/-! # Ordered row containment under bounded block maps -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.Deuber

def IsLeadingEmbedding {ι κ : Type*} [Preorder ι] [Preorder κ]
    (T : Matrix ι κ ℤ) (e : ι ↪o κ) (c : ℤ) : Prop :=
  IsBlockEmbedding T ∧ ∀ i, T i (e i) = c ∧ ∀ j, e i < j → T i j = 0

theorem IsLeadingEmbedding.row_subset_mul {ι κ : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    {T : Matrix ι κ ℤ} {e : ι ↪o κ} {c d : ℤ} {p L K : ℕ}
    (hT : IsLeadingEmbedding T e d) (hd : d ≠ 0) (hp : p ≤ L)
    (hcL : |c| ≤ (L : ℤ)) (hbound : ∀ i k, |T i k| ≤ (K : ℤ))
    (S : κ → ℤ) (j : ι) :
    row p c (T.mulVec S) j ⊆ row (L * K) (c * d) S (e j) := by
  intro x hx
  obtain ⟨w, hwj, hwbefore, hwafter, hx⟩ := mem_row_iff_coefficients.mp hx
  have hwbound : ∀ i, |w i| ≤ (L : ℤ) := by
    intro i
    rcases lt_trichotomy i j with hi | hi | hi
    · have h := hwbefore i hi
      have hp' : (p : ℤ) ≤ (L : ℤ) := by exact_mod_cast hp
      exact abs_le.mpr ⟨by linarith [h.1], h.2.trans hp'⟩
    · subst i
      simpa [hwj] using hcL
    · simp [hwafter i hi]
  let a := Matrix.vecMul w T
  have habound : ∀ k, |a k| ≤ (L : ℤ) * (K : ℤ) := by
    intro k
    by_cases hk : ∃ i, T i k ≠ 0
    · obtain ⟨i, hi⟩ := hk
      change |Matrix.vecMul w T k| ≤ _
      rw [hT.1.vecMul_apply_of_ne_zero w hi, abs_mul]
      exact mul_le_mul (hwbound i) (hbound i k) (abs_nonneg _) (by positivity)
    · push_neg at hk
      simp only [a, Matrix.vecMul, dotProduct, hk, mul_zero,
        Finset.sum_const_zero, abs_zero]
      positivity
  have haj : a (e j) = c * d := by
    change Matrix.vecMul w T (e j) = _
    have hne : T j (e j) ≠ 0 := by rw [(hT.2 j).1]; exact hd
    rw [hT.1.vecMul_apply_of_ne_zero w hne, hwj, (hT.2 j).1]
  have haafter : ∀ k, e j < k → a k = 0 := by
    intro k hk
    apply Finset.sum_eq_zero
    intro i _
    change w i * T i k = 0
    by_cases hi : i ≤ j
    · have hik : e i < k := lt_of_le_of_lt (e.monotone hi) hk
      rw [(hT.2 i).2 k hik, mul_zero]
    · rw [hwafter i (lt_of_not_ge hi), zero_mul]
  have hsum : x = ∑ k, a k * S k := by
    rw [hx]
    exact Matrix.dotProduct_mulVec w T S
  rw [hsum]
  apply sum_mem_row_of_coefficients haj _ haafter
  intro k _
  simpa only [Nat.cast_mul] using abs_le.mp (habound k)

theorem IsLeadingEmbedding.row_subset {ι κ : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    {T : Matrix ι κ ℤ} {e : ι ↪o κ} {c : ℤ} {p L : ℕ}
    (hT : IsLeadingEmbedding T e c) (hc : c ≠ 0) (hp : p ≤ L)
    (hcL : |c| ≤ (L : ℤ)) (hbound : ∀ i k, |T i k| ≤ (L : ℤ))
    (S : κ → ℤ) (j : ι) :
    row p c (T.mulVec S) j ⊆ row (L * L) (c * c) S (e j) :=
  hT.row_subset_mul hc hp hcL hbound S j

theorem IsLeadingEmbedding.pattern_subset {ι κ : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    {T : Matrix ι κ ℤ} {e : ι ↪o κ} {c : ℤ} {p L : ℕ}
    (hT : IsLeadingEmbedding T e c) (hc : c ≠ 0) (hp : p ≤ L)
    (hcL : |c| ≤ (L : ℤ)) (hbound : ∀ i k, |T i k| ≤ (L : ℤ))
    (S : κ → ℤ) :
    pattern p c (T.mulVec S) ⊆ pattern (L * L) (c * c) S := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact row_subset_pattern _ _ _ (e j) (hT.row_subset hc hp hcL hbound S j hj)

end Sidon.Deuber
