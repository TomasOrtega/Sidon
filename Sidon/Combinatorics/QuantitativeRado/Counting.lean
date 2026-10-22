import Sidon.Combinatorics.Deuber.Basic

/-! # Fiber bounds for disjoint-support integer maps -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon

theorem IsBlockEmbedding.card_fiber_pi_le {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (f : κ → α → ℤ) (hf : ∀ j, Function.Injective (f j))
    (y : ι → ℤ) :
    Fintype.card {Y : κ → α // T.mulVec (fun j => f j (Y j)) = y} ≤
      Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
  obtain ⟨e, he⟩ := hT.exists_pivots
  let Off := {j : κ // j ∉ Set.range e}
  let restrict : {Y : κ → α // T.mulVec (fun j => f j (Y j)) = y} → Off → α :=
    fun Y j => Y.val j.val
  have hinj : Function.Injective restrict := by
    intro Y Y' hYY'
    have hoff : ∀ j : κ, j ∉ Set.range e → Y.val j = Y'.val j := by
      intro j hj
      exact congrFun hYY' ⟨j, hj⟩
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      have hrow : ∑ k, T i k * (f k (Y.val k) - f k (Y'.val k)) = 0 := by
        have h := congrFun (Y.property.trans Y'.property.symm) i
        simpa [Matrix.mulVec, Matrix.dotProduct, Function.comp_apply,
          mul_sub, Finset.sum_sub_distrib] using sub_eq_zero.mpr h
      have hsum : (∑ k, T i k * (f k (Y.val k) - f k (Y'.val k))) =
          T i (e i) * (f (e i) (Y.val (e i)) - f (e i) (Y'.val (e i))) := by
        apply Fintype.sum_eq_single (e i)
        intro k hki
        by_cases hk : k ∈ Set.range e
        · obtain ⟨i', rfl⟩ := hk
          have hii' : i ≠ i' := by
            intro h
            subst i'
            exact hki rfl
          have hzero : T i (e i') = 0 :=
            (hT.2 i i' (e i') hii').resolve_right (he i')
          simp [hzero]
        · rw [hoff k hk, sub_self, mul_zero]
      rw [hsum] at hrow
      exact hf (e i) (sub_eq_zero.mp ((mul_eq_zero.mp hrow).resolve_left (he i)))
    · exact hoff j hj
  calc
    Fintype.card {Y : κ → α // T.mulVec (fun j => f j (Y j)) = y} ≤ Fintype.card (Off → α) :=
      Fintype.card_le_of_injective restrict hinj
    _ = Fintype.card α ^ Fintype.card Off := Fintype.card_fun
    _ = Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
      congr 1
      exact (Fintype.card_subtype_compl (fun j => j ∈ Set.range e)).trans
        (congrArg (fun n => Fintype.card κ - n) (Fintype.card_range e))

theorem IsBlockEmbedding.card_fiber_le {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (f : α → ℤ) (hf : Function.Injective f) (y : ι → ℤ) :
    Fintype.card {Y : κ → α // T.mulVec (f ∘ Y) = y} ≤
      Fintype.card α ^ (Fintype.card κ - Fintype.card ι) :=
  hT.card_fiber_pi_le (fun _ => f) (fun _ => hf) y

theorem IsBlockEmbedding.card_fiber_postcompose_pi_le {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (f : κ → α → ℤ) (hf : ∀ j, Function.Injective (f j))
    (g : (ι → ℤ) → β) (hg : Function.Injective g) (x : β) :
    Fintype.card {Y : κ → α // g (T.mulVec (fun j => f j (Y j))) = x} ≤
      Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
  by_cases h : Nonempty {Y : κ → α // g (T.mulVec (fun j => f j (Y j))) = x}
  · obtain ⟨Y₀⟩ := h
    let e : {Y : κ → α // g (T.mulVec (fun j => f j (Y j))) = x} →
        {Y : κ → α // T.mulVec (fun j => f j (Y j)) =
          T.mulVec (fun j => f j (Y₀.val j))} :=
      fun Y => ⟨Y.val, hg (Y.property.trans Y₀.property.symm)⟩
    have he : Function.Injective e := by
      intro Y Y' hYY'
      apply Subtype.ext
      change (e Y).val = (e Y').val
      exact congrArg Subtype.val hYY'
    exact (Fintype.card_le_of_injective e he).trans
      (hT.card_fiber_pi_le f hf (T.mulVec (fun j => f j (Y₀.val j))))
  · letI : IsEmpty {Y : κ → α // g (T.mulVec (fun j => f j (Y j))) = x} :=
      not_nonempty_iff.mp h
    simp

theorem card_blockFamily_pi_fiber_le {η ι κ α β : Type*}
    [Fintype η] [Fintype ι] [Fintype κ] [Fintype α]
    (T : η → Matrix ι κ ℤ) (hT : ∀ j, IsBlockEmbedding (T j))
    (f : κ → α → ℤ) (hf : ∀ j, Function.Injective (f j))
    (g : (ι → ℤ) → β) (hg : Function.Injective g) (x : β) :
    Fintype.card {Y : κ → α // ∃ j, g ((T j).mulVec (fun k => f k (Y k))) = x} ≤
      Fintype.card η * Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
  let assign : {Y : κ → α // ∃ j, g ((T j).mulVec (fun k => f k (Y k))) = x} →
      (j : η) × {Y : κ → α // g ((T j).mulVec (fun k => f k (Y k))) = x} :=
    fun Y => ⟨Y.property.choose, ⟨Y.val, Y.property.choose_spec⟩⟩
  have hinj : Function.Injective assign := by
    intro Y Y' hYY'
    apply Subtype.ext
    exact congrArg (fun z : (j : η) ×
      {Y : κ → α // g ((T j).mulVec (fun k => f k (Y k))) = x} => z.2.val) hYY'
  calc
    Fintype.card {Y : κ → α // ∃ j, g ((T j).mulVec (fun k => f k (Y k))) = x} ≤
        Fintype.card ((j : η) ×
          {Y : κ → α // g ((T j).mulVec (fun k => f k (Y k))) = x}) :=
      Fintype.card_le_of_injective assign hinj
    _ = ∑ j, Fintype.card
        {Y : κ → α // g ((T j).mulVec (fun k => f k (Y k))) = x} :=
      Fintype.card_sigma
    _ ≤ ∑ _j : η, Fintype.card α ^ (Fintype.card κ - Fintype.card ι) :=
      Finset.sum_le_sum fun j _ => (hT j).card_fiber_postcompose_pi_le f hf g hg x
    _ = Fintype.card η * Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by simp

theorem IsBlockEmbedding.card_fiber_postcompose_le {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] {T : Matrix ι κ ℤ}
    (hT : IsBlockEmbedding T) (f : α → ℤ) (hf : Function.Injective f)
    (g : (ι → ℤ) → β) (hg : Function.Injective g) (x : β) :
    Fintype.card {Y : κ → α // g (T.mulVec (f ∘ Y)) = x} ≤
      Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
  by_cases h : Nonempty {Y : κ → α // g (T.mulVec (f ∘ Y)) = x}
  · obtain ⟨Y₀⟩ := h
    let e : {Y : κ → α // g (T.mulVec (f ∘ Y)) = x} →
        {Y : κ → α // T.mulVec (f ∘ Y) = T.mulVec (f ∘ Y₀.val)} :=
      fun Y => ⟨Y.val, hg (Y.property.trans Y₀.property.symm)⟩
    have he : Function.Injective e := by
      intro Y Y' hYY'
      apply Subtype.ext
      change (e Y).val = (e Y').val
      exact congrArg Subtype.val hYY'
    exact (Fintype.card_le_of_injective e he).trans
      (hT.card_fiber_le f hf (T.mulVec (f ∘ Y₀.val)))
  · letI : IsEmpty {Y : κ → α // g (T.mulVec (f ∘ Y)) = x} :=
      not_nonempty_iff.mp h
    simp

theorem card_blockFamily_fiber_le {η ι κ α β : Type*}
    [Fintype η] [Fintype ι] [Fintype κ] [Fintype α]
    (T : η → Matrix ι κ ℤ) (hT : ∀ j, IsBlockEmbedding (T j))
    (f : α → ℤ) (hf : Function.Injective f)
    (g : (ι → ℤ) → β) (hg : Function.Injective g) (x : β) :
    Fintype.card {Y : κ → α // ∃ j, g ((T j).mulVec (f ∘ Y)) = x} ≤
      Fintype.card η * Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
  let assign : {Y : κ → α // ∃ j, g ((T j).mulVec (f ∘ Y)) = x} →
      (j : η) × {Y : κ → α // g ((T j).mulVec (f ∘ Y)) = x} :=
    fun Y => ⟨Y.property.choose, ⟨Y.val, Y.property.choose_spec⟩⟩
  have hinj : Function.Injective assign := by
    intro Y Y' hYY'
    apply Subtype.ext
    exact congrArg (fun z : (j : η) × {Y : κ → α // g ((T j).mulVec (f ∘ Y)) = x} =>
      z.2.val) hYY'
  calc
    Fintype.card {Y : κ → α // ∃ j, g ((T j).mulVec (f ∘ Y)) = x} ≤
        Fintype.card ((j : η) × {Y : κ → α // g ((T j).mulVec (f ∘ Y)) = x}) :=
      Fintype.card_le_of_injective assign hinj
    _ = ∑ j, Fintype.card {Y : κ → α // g ((T j).mulVec (f ∘ Y)) = x} :=
      Fintype.card_sigma
    _ ≤ ∑ _j : η, Fintype.card α ^ (Fintype.card κ - Fintype.card ι) :=
      Finset.sum_le_sum fun j _ => (hT j).card_fiber_postcompose_le f hf g hg x
    _ = Fintype.card η * Fintype.card α ^ (Fintype.card κ - Fintype.card ι) := by
      simp

end Sidon
