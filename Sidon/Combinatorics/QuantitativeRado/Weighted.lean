import Sidon.Combinatorics.QuantitativeRado

/-! # Bounded-weight consequence of quantitative Rado -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.QuantitativeRado

theorem exists_one_div_le_of_sum_eq_one {r : ℕ} (hr : 0 < r)
    (w : Fin r → ℝ) (hw : ∑ i, w i = 1) : ∃ i, 1 / (r : ℝ) ≤ w i := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have hsum : ∑ j, w j ≤ ∑ _j : Fin r, w i :=
    Finset.sum_le_sum fun j _ => hmax j (Finset.mem_univ j)
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact ⟨i, (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).mpr (by nlinarith)⟩

theorem class_card_mul_pow_le_weightedSolutionCount {ι : Type*} [Fintype ι]
    (A C : Finset ℤ) (hCA : C ⊆ A) (a : ι → ℤ) (f : ℤ → ℝ)
    (hf : ∀ x ∈ A, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t)
    (hC : ∀ x ∈ C, t ≤ f x) :
    (linearSolutions C a).card * t ^ Fintype.card ι ≤
      weightedSolutionCount A a (fun _ => f) := by
  have hsub : linearSolutions C a ⊆ linearSolutions A a := by
    intro x hx
    obtain ⟨hcoords, hzero⟩ := mem_linearSolutions C a x |>.mp hx
    exact mem_linearSolutions A a x |>.mpr ⟨fun i => hCA (hcoords i), hzero⟩
  calc
    _ = ∑ _x ∈ linearSolutions C a, t ^ Fintype.card ι := by simp
    _ ≤ ∑ x ∈ linearSolutions C a, ∏ i, f (x i) := by
      apply Finset.sum_le_sum
      intro x hx
      have hprod : (∏ _i : ι, t) ≤ ∏ i, f (x i) :=
        Finset.prod_le_prod₀ (fun _ _ => ht)
          (fun i _ => hC _ (((mem_linearSolutions C a x).mp hx).1 i))
      simpa only [Finset.prod_const, Finset.card_univ] using hprod
    _ ≤ ∑ x ∈ linearSolutions A a, ∏ i, f (x i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      exact Finset.prod_nonneg fun i _ => hf _ (((mem_linearSolutions A a x).mp hx).1 i)
    _ = _ := rfl

theorem exists_weighted_count_of_class_count {s r q N : ℕ} (hr : 0 < r)
    (a : Fin s → ℤ) (δ : ℝ)
    (hcount : ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
      δ * (N : ℝ) ^ q ≤
        (linearSolutions ((interval N).filter (fun x => χ x = colour)) a).card)
    (g : Fin r → ℤ → ℝ) (hg : ∀ j, ∀ x ∈ interval N, 0 ≤ g j x)
    (hsum : ∀ x ∈ interval N, ∑ j, g j x = 1) :
    ∃ colour : Fin r,
      (δ / (r : ℝ) ^ s) * (N : ℝ) ^ q ≤
        weightedSolutionCount (interval N) a (fun _ => g colour) := by
  have hex : ∀ x : ℤ, ∃ j : Fin r, x ∈ interval N → 1 / (r : ℝ) ≤ g j x := by
    intro x
    by_cases hx : x ∈ interval N
    · obtain ⟨j, hj⟩ := exists_one_div_le_of_sum_eq_one hr (fun j => g j x) (hsum x hx)
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, hr⟩, fun h => (hx h).elim⟩
  choose χ hχ using hex
  obtain ⟨j, hj⟩ := hcount χ
  let C := (interval N).filter (fun x => χ x = j)
  have hbound := class_card_mul_pow_le_weightedSolutionCount (interval N) C
    (Finset.filter_subset _ _) a (g j) (hg j) (1 / (r : ℝ)) (by positivity) (by
      intro x hx
      obtain ⟨hxN, hxj⟩ := Finset.mem_filter.mp hx
      simpa only [hxj] using hχ x hxN)
  have hscale : δ * (N : ℝ) ^ q * (1 / (r : ℝ)) ^ s ≤
      (linearSolutions C a).card * (1 / (r : ℝ)) ^ s :=
    mul_le_mul_of_nonneg_right hj (by positivity)
  refine ⟨j, ?_⟩
  have h := hscale.trans (by simpa only [Fintype.card_fin] using hbound)
  convert h using 1
  ring

theorem exists_many_weighted_linearSolutions {s r : ℕ}
    (hs : 2 ≤ s) (hr : 0 < r) (a : Fin s → ℤ) (ha : ∀ i, a i ≠ 0)
    (I : Finset (Fin s)) (hIne : I.Nonempty) (hI : ∑ i ∈ I, a i = 0) :
    ∃ N₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ g : Fin r → ℤ → ℝ,
        (∀ j, ∀ x ∈ interval N, 0 ≤ g j x) →
        (∀ x ∈ interval N, ∑ j, g j x = 1) →
        ∃ colour : Fin r, δ * (N : ℝ) ^ (s - 1) ≤
          weightedSolutionCount (interval N) a (fun _ => g colour) := by
  obtain ⟨N₀, δ, hδ, hcount⟩ :=
    exists_many_monochromatic_linearSolutions hs hr a ha I hIne hI
  refine ⟨N₀, δ / (r : ℝ) ^ s, by positivity, ?_⟩
  intro N hN g hg hsum
  exact exists_weighted_count_of_class_count hr a δ (hcount N hN) g hg hsum

end Sidon.QuantitativeRado
