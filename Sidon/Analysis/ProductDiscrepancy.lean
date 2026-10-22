import Sidon.Analysis.FiniteHolder
import Mathlib.Tactic

/-! # A finite product difference bounded by single-factor differences -/

noncomputable section

open scoped BigOperators

namespace Sidon

theorem norm_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℂ) (b : ι → ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ b i) (hg : ∀ i ∈ s, ‖g i‖ ≤ b i) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤
      ∑ i ∈ s, ‖f i - g i‖ * ∏ j ∈ s.erase i, b j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ b i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ b i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hb : ∀ i ∈ s, 0 ≤ b i := fun i hi => (norm_nonneg _).trans (hfs i hi)
    have hba : 0 ≤ b a := (norm_nonneg _).trans (hf a (Finset.mem_insert_self _ _))
    have hp : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, b i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfs
    have hsplit : (f a * ∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i =
        (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    have hsum : 0 ≤ ∑ i ∈ s, ‖f i - g i‖ * ∏ j ∈ s.erase i, b j := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j hj => hb j (Finset.mem_of_mem_erase hj))
    have hmain : ‖(f a * ∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ ≤
        ‖f a - g a‖ * (∏ i ∈ s, b i) +
          b a * (∑ i ∈ s, ‖f i - g i‖ * ∏ j ∈ s.erase i, b j) := by
      rw [hsplit]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
        (mul_le_mul (hg a (Finset.mem_insert_self _ _)) (ih hfs hgs) (norm_nonneg _) hba)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    apply hmain.trans_eq
    rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := by intro h; exact ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert (by
      intro hh
      exact ha (Finset.mem_of_mem_erase hh))]
    ring

end Sidon
