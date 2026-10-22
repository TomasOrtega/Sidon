import Sidon.Combinatorics.QuantitativeRado.Counting
import Sidon.Combinatorics.QuantitativeRado.Seeds
import Sidon.Transference.Counting

/-! # Quantitative counting from a Deuber kernel parametrization -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.QuantitativeRado

private theorem card_congr_explicit {α β : Type*} (F : Fintype α) (G : Fintype β)
    (e : α ≃ β) : @Fintype.card α F = @Fintype.card β G :=
  @Fintype.card_congr α β F G e

theorem card_le_mul_of_fiber_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (B : ℕ) (hB : ∀ b, Fintype.card {a // f a = b} ≤ B) :
    Fintype.card α ≤ Fintype.card β * B := by
  let assign : α → (b : β) × {a // f a = b} := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hinj : Function.Injective assign := by
    intro a a' h
    exact congrArg (fun x : (b : β) × {a // f a = b} => x.2.val) h
  calc
    Fintype.card α ≤ Fintype.card ((b : β) × {a // f a = b}) :=
      Fintype.card_le_of_injective assign hinj
    _ = ∑ b, Fintype.card {a // f a = b} := Fintype.card_sigma
    _ ≤ ∑ _b : β, B := Finset.sum_le_sum fun b _ => hB b
    _ = Fintype.card β * B := by simp

theorem card_seed_family_fiber_le {η β : Type*} [Fintype η] {M q L R : ℕ}
    (T : η → Matrix (Fin q) (Fin M) ℤ) (hT : ∀ j, IsBlockEmbedding (T j))
    (g : (Fin q → ℤ) → β) (hg : Function.Injective g) (x : β) :
    Fintype.card {u : Fin M → Fin L // ∃ j,
      g ((T j).mulVec (seedVector M L R u)) = x} ≤
      Fintype.card η * L ^ (M - q) := by
  classical
  have h := card_blockFamily_pi_fiber_le T hT (seedValue L R)
    (seedValue_injective L R) g hg x
  simp only [Fintype.card_fin] at h
  convert h using 1
  exact card_congr_explicit _ _ (Equiv.refl _)

theorem card_seed_assignment_le {η β γ : Type*} [Fintype η] [Fintype γ]
    {M q L R : ℕ} (T : η → Matrix (Fin q) (Fin M) ℤ)
    (hT : ∀ j, IsBlockEmbedding (T j))
    (g : (Fin q → ℤ) → β) (hg : Function.Injective g)
    (selected : (Fin M → Fin L) → η) (assign : (Fin M → Fin L) → γ)
    (project : γ → β)
    (hassign : ∀ u, project (assign u) =
      g ((T (selected u)).mulVec (seedVector M L R u))) :
    L ^ M ≤ Fintype.card γ * (Fintype.card η * L ^ (M - q)) := by
  have hfiber : ∀ x : γ,
      Fintype.card {u // assign u = x} ≤ Fintype.card η * L ^ (M - q) := by
    intro x
    let e : {u // assign u = x} →
        {u : Fin M → Fin L // ∃ j,
          g ((T j).mulVec (seedVector M L R u)) = project x} :=
      fun u => ⟨u.val, selected u.val,
        (hassign u.val).symm.trans (congrArg project u.property)⟩
    have he : Function.Injective e := by
      intro u v huv
      apply Subtype.ext
      change (e u).val = (e v).val
      exact congrArg Subtype.val huv
    apply (Fintype.card_le_of_injective e he).trans
    exact card_seed_family_fiber_le (M := M) (q := q) (L := L) (R := R) T hT g hg _
  have h := card_le_mul_of_fiber_le assign _ hfiber
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

theorem exists_many_monochromatic_of_pattern_map {s q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (p c : ℕ) (hp : 0 < p) (hc : 0 < c)
    (a : Fin s → ℤ) (g : (Fin q → ℤ) → (Fin s → ℤ))
    (hg : Function.Injective g)
    (hpattern : ∀ y i, g y i ∈ Deuber.pattern p (c : ℤ) y)
    (hzero : ∀ y, ∑ i, a i * g y i = 0) :
    ∃ N₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
        δ * (N : ℝ) ^ q ≤
          (linearSolutions ((interval N).filter (fun x => χ x = colour)) a).card := by
  classical
  obtain ⟨M, hqM, P, C, hP, hC, family, hfinite, hblock, hextract⟩ :=
    Deuber.exists_finite_extraction q p c r hq hp hc hr
  letI : Fintype family := hfinite.fintype
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hfamily : Nonempty family := by
    obtain ⟨T, hT, _⟩ := hextract (fun _ => 0) (fun _ => ⟨0, hr⟩)
    exact ⟨⟨T, hT⟩⟩
  letI : Nonempty family := hfamily
  let F := Fintype.card family
  let H := (2 * C + 1) * (4 * P + 2) ^ M
  have hF : 0 < F := Fintype.card_pos_iff.mpr hfamily
  have hH : 0 < H := by dsimp [H]; positivity
  let δ : ℝ := 1 / ((r : ℝ) * F * (2 * (H : ℝ)) ^ q)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨2 * H, δ, hδ, ?_⟩
  intro N hN χ
  obtain ⟨L, hL, hNL, hpositive⟩ := exists_positive_seed_box M P C hC N hN
  have hex : ∀ u : Fin M → Fin L, ∃ T : family,
      Deuber.pattern p (c : ℤ) (T.val.mulVec (seedVector M L (4 * P + 2) u)) ⊆
        Deuber.pattern P (C : ℤ) (seedVector M L (4 * P + 2) u) ∧
      Deuber.IsMonochromatic χ
        (Deuber.pattern p (c : ℤ) (T.val.mulVec (seedVector M L (4 * P + 2) u))) := by
    intro u
    obtain ⟨T, hT, hsub, hmono⟩ := hextract (seedVector M L (4 * P + 2) u) χ
    exact ⟨⟨T, hT⟩, hsub, hmono⟩
  choose T hsub hmono using hex
  let output := fun u : Fin M → Fin L =>
    g ((T u).val.mulVec (seedVector M L (4 * P + 2) u))
  let S := fun colour : Fin r =>
    linearSolutions ((interval N).filter (fun x => χ x = colour)) a
  have hsolution : ∀ u, ∃ colour, output u ∈ S colour := by
    intro u
    obtain ⟨colour, hcolour⟩ := hmono u
    refine ⟨colour, mem_linearSolutions _ _ _ |>.mpr ⟨?_, hzero _⟩⟩
    intro i
    have hm := hpattern ((T u).val.mulVec (seedVector M L (4 * P + 2) u)) i
    have hi := hpositive u (hsub u hm)
    exact Finset.mem_filter.mpr ⟨mem_interval.mpr hi, hcolour _ hm⟩
  choose colour hcolour using hsolution
  let Out := (j : Fin r) × {x // x ∈ S j}
  let assign : (Fin M → Fin L) → Out := fun u => ⟨colour u, ⟨output u, hcolour u⟩⟩
  have hcount : L ^ M ≤ Fintype.card Out * (F * L ^ (M - q)) :=
    card_seed_assignment_le (M := M) (q := q) (L := L) (R := 4 * P + 2)
      (fun V : family => V.val) (fun V => hblock V.val V.property) g hg T assign
      (fun v : Out => v.2.val) (fun _ => rfl)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin r => (S j).card) Finset.univ_nonempty
  have hcardOut : Fintype.card Out ≤ r * (S j).card := by
    calc
      Fintype.card Out = ∑ j : Fin r, (S j).card := by simp [Out, Fintype.card_sigma]
      _ ≤ ∑ _k : Fin r, (S j).card :=
        Finset.sum_le_sum fun k _ => hmax k (Finset.mem_univ k)
      _ = r * (S j).card := by simp
  have hcount' : L ^ M ≤ (r * (S j).card * F) * L ^ (M - q) := by
    have h := hcount.trans (Nat.mul_le_mul_right (F * L ^ (M - q)) hcardOut)
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using h
  have hLpow : 0 < L ^ (M - q) := pow_pos hL _
  have hLq : L ^ q ≤ r * (S j).card * F := by
    apply Nat.le_of_mul_le_mul_right _ hLpow
    convert hcount' using 1
    rw [← pow_add, Nat.add_sub_of_le hqM]
  have hLq' : (L : ℝ) ^ q ≤ (r : ℝ) * F * (S j).card := by
    have h := (by exact_mod_cast hLq : (L : ℝ) ^ q ≤ r * (S j).card * F)
    nlinarith
  have hNL' : (N : ℝ) / (2 * (H : ℝ)) ≤ L := by
    simpa only [H, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_one, Nat.cast_ofNat] using hNL
  have hpow := (pow_le_pow_left (by positivity : (0 : ℝ) ≤ (N : ℝ) /
      (2 * (H : ℝ))) hNL' q).trans hLq'
  rw [div_pow] at hpow
  have hnum := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * (H : ℝ)) ^ q)).mp hpow
  refine ⟨j, ?_⟩
  change δ * (N : ℝ) ^ q ≤ (S j).card
  dsimp only [δ]
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity :
    (0 : ℝ) < (r : ℝ) * F * (2 * (H : ℝ)) ^ q)).mpr
  nlinarith

end Sidon.QuantitativeRado
