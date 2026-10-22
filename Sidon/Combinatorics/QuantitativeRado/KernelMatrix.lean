import Sidon.Combinatorics.Deuber.Selection

/-! # An integral kernel parametrization with a common positive leading coefficient -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.QuantitativeRado

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mulVec_injective_of_pivot_rows (C : Matrix ι ι ℤ) (c : ℤ) (hc : c ≠ 0)
    (R : Finset ι)
    (hrows : ∀ i ∈ R, ∀ j, C i j = if j = i then c else 0)
    (hcols : ∀ i j, j ∉ R → C i j = if j = i then c else 0) :
    Function.Injective C.mulVec := by
  intro y z hyz
  have hselected : ∀ i ∈ R, y i = z i := by
    intro i hi
    have h := congrFun hyz i
    change (∑ j, C i j * y j) = ∑ j, C i j * z j at h
    simp only [hrows i hi, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at h
    exact mul_left_cancel₀ hc h
  funext i
  by_cases hi : i ∈ R
  · exact hselected i hi
  · have hsum : (∑ j, C i j * (y j - z j)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun hyz i)
    have heq : (∑ j, C i j * (y j - z j)) = c * (y i - z i) := by
      rw [Finset.sum_eq_single i]
      · rw [hcols i i hi, if_pos rfl]
      · intro j _ hji
        by_cases hj : j ∈ R
        · rw [hselected j hj, sub_self, mul_zero]
        · rw [hcols i j hj, if_neg hji, zero_mul]
      · simp
    rw [heq] at hsum
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hc)

/-- The positive denominator used simultaneously for every kernel column. -/
def pivotScale (a : ι → ℤ) (p : ι) : ℤ := (a p).natAbs

def compensatedColumn (a : ι → ℤ) (p j : ι) (i : ι) : ℤ :=
  (if i = j then pivotScale a p else 0) -
    (if i = p then (a p).sign * a j else 0)

theorem compensatedColumn_kernel (a : ι → ℤ) (p j : ι) :
    (∑ i, a i * compensatedColumn a p j i) = 0 := by
  simp only [compensatedColumn, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold pivotScale
  calc
    a j * ↑(a p).natAbs - a p * ((a p).sign * a j) =
        a j * ↑(a p).natAbs - (a p * (a p).sign) * a j := by ring
    _ = 0 := by rw [Int.mul_sign]; ring

omit [Fintype ι] in
theorem compensatedColumn_apply {a : ι → ℤ} {p i j : ι} (hip : i ≠ p) :
    compensatedColumn a p j i = if i = j then pivotScale a p else 0 := by
  simp only [compensatedColumn, if_neg hip, sub_zero]

def insideSeed (a : ι → ℤ) (p : ι) (I : Finset ι) (i : ι) : ℤ :=
  if i ∈ I then pivotScale a p else 0

def outsideSeed (a : ι → ℤ) (p : ι) (I : Finset ι) (i : ι) : ℤ :=
  (if i ∈ I then 0 else pivotScale a p) -
    (if i = p then (a p).sign * ∑ j ∈ Finset.univ \ I, a j else 0)

theorem insideSeed_kernel (a : ι → ℤ) (p : ι) (I : Finset ι)
    (hI : ∑ i ∈ I, a i = 0) : (∑ i, a i * insideSeed a p I i) = 0 := by
  simp only [insideSeed, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, hI, zero_mul]

theorem outsideSeed_kernel (a : ι → ℤ) (p : ι) (I : Finset ι) :
    (∑ i, a i * outsideSeed a p I i) = 0 := by
  simp only [outsideSeed, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hfilter : Finset.univ.filter (fun i => i ∉ I) = Finset.univ \ I := by ext; simp
  rw [hfilter, ← Finset.sum_mul]
  unfold pivotScale
  calc
    (∑ i ∈ Finset.univ \ I, a i) * ↑(a p).natAbs -
        a p * ((a p).sign * ∑ i ∈ Finset.univ \ I, a i) =
      (∑ i ∈ Finset.univ \ I, a i) * ↑(a p).natAbs -
        (a p * (a p).sign) * ∑ i ∈ Finset.univ \ I, a i := by ring
    _ = 0 := by rw [Int.mul_sign]; ring

theorem outsideSeed_apply {a : ι → ℤ} {p i : ι} (I : Finset ι) (hip : i ≠ p) :
    outsideSeed a p I i = if i ∈ I then 0 else pivotScale a p := by
  simp only [outsideSeed, if_neg hip, sub_zero]

def kernelColumns (a : ι → ℤ) (p : ι) (I : Finset ι)
    (j₀ : {i : ι // i ≠ p}) (j₁ : Option {i : ι // i ≠ p}) :
    Matrix ι {i : ι // i ≠ p} ℤ := fun i j =>
  if j = j₀ then insideSeed a p I i else
    if some j = j₁ then outsideSeed a p I i else compensatedColumn a p j i

theorem kernelColumns_kernel (a : ι → ℤ) (p : ι) (I : Finset ι)
    (hI : ∑ i ∈ I, a i = 0) (j₀ : {i : ι // i ≠ p})
    (j₁ : Option {i : ι // i ≠ p}) (j : {i : ι // i ≠ p}) :
    (∑ i, a i * kernelColumns a p I j₀ j₁ i j) = 0 := by
  unfold kernelColumns
  split_ifs
  · exact insideSeed_kernel a p I hI
  · exact outsideSeed_kernel a p I
  · exact compensatedColumn_kernel a p j

theorem kernelColumns_injective (a : ι → ℤ) (p : ι) (I : Finset ι)
    (ha : a p ≠ 0) (j₀ : {i : ι // i ≠ p}) (hj₀ : (j₀ : ι) ∈ I)
    (j₁ : Option {i : ι // i ≠ p})
    (hj₁ : ∀ j, some j = j₁ → (j : ι) ∉ I) :
    Function.Injective (kernelColumns a p I j₀ j₁).mulVec := by
  let C := kernelColumns a p I j₀ j₁
  let D : Matrix {i : ι // i ≠ p} {i : ι // i ≠ p} ℤ := fun i j => C i j
  let R : Finset {i : ι // i ≠ p} := insert j₀ j₁.toFinset
  have hc : pivotScale a p ≠ 0 := by
    unfold pivotScale
    exact_mod_cast (Int.natAbs_pos.mpr ha).ne'
  have hentry (i j : {i : ι // i ≠ p}) : D i j =
      if j = j₀ then (if (i : ι) ∈ I then pivotScale a p else 0) else
      if some j = j₁ then (if (i : ι) ∈ I then 0 else pivotScale a p) else
      if i = j then pivotScale a p else 0 := by
    simp only [D, C, kernelColumns, insideSeed, outsideSeed_apply I i.property,
      compensatedColumn_apply i.property, Subtype.coe_inj]
  have hR : ∀ i ∈ R, i = j₀ ∨ some i = j₁ := by
    intro i hi
    cases j₁ with
    | none => simpa [R] using hi
    | some j => simpa [R, eq_comm] using hi
  have hrows : ∀ i ∈ R, ∀ j, D i j = if j = i then pivotScale a p else 0 := by
    intro i hi j
    rw [hentry]
    rcases hR i hi with hi₀ | hi₁
    · subst i
      by_cases hj : j = j₀
      · simp [hj, hj₀]
      · by_cases hj' : some j = j₁
        · simp [hj, hj', hj₀]
        · simp [hj, hj', Ne.symm hj]
    · have hiout : (i : ι) ∉ I := hj₁ i hi₁
      have hi0 : i ≠ j₀ := by intro h; subst i; exact hiout hj₀
      by_cases hj : j = j₀
      · simp [hj, hiout, hi0, Ne.symm hi0]
      · by_cases hj' : some j = j₁
        · have hji : j = i := Option.some.inj (hj'.trans hi₁.symm)
          simp [hji, hi0, hi₁, hiout]
        · have hji : j ≠ i := by intro h; subst j; exact hj' hi₁
          simp [hj, hj', hji, Ne.symm hji]
  have hcols : ∀ i j, j ∉ R → D i j = if j = i then pivotScale a p else 0 := by
    intro i j hj
    have hj0 : j ≠ j₀ := fun h => hj (by simp [R, h])
    have hj1 : some j ≠ j₁ := fun h => hj (by simp [R, ← h])
    rw [hentry, if_neg hj0, if_neg hj1]
    simp only [eq_comm]
  have hD := mulVec_injective_of_pivot_rows D (pivotScale a p) hc R hrows hcols
  intro y z hyz
  apply hD
  funext i
  exact congrFun hyz i

omit [DecidableEq ι] in
theorem matrix_weighted_sum_mulVec_eq_zero {κ : Type*} [Fintype κ]
    (a : ι → ℤ) (B : Matrix ι κ ℤ) (hB : ∀ j, (∑ i, a i * B i j) = 0)
    (y : κ → ℤ) : (∑ i, a i * (B.mulVec y) i) = 0 := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, hB, zero_mul, Finset.sum_const_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem mulVec_injective_reindex_columns {κ : Type*} [Fintype κ]
    {κ' : Type*} [Fintype κ'] (B : Matrix ι κ ℤ)
    (hB : Function.Injective B.mulVec) (e : κ' ≃ κ) :
    Function.Injective (B.submatrix id e).mulVec := by
  apply Matrix.mulVec_injective_iff.mpr
  exact (Matrix.mulVec_injective_iff.mp hB).comp e e.injective

theorem exists_equiv_fin_last {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : ℕ} (hcard : Fintype.card κ = q) (hq : 0 < q) (j₀ : κ) :
    ∃ e : Fin q ≃ κ, e ⟨q - 1, by omega⟩ = j₀ := by
  let e₀ : Fin q ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let last : Fin q := ⟨q - 1, by omega⟩
  refine ⟨(Equiv.swap last (e₀.symm j₀)).trans e₀, ?_⟩
  simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

theorem exists_equiv_fin_last_two {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : ℕ} (hcard : Fintype.card κ = q) (hq : 2 ≤ q) (j₀ j₁ : κ) (hne : j₀ ≠ j₁) :
    ∃ e : Fin q ≃ κ, e ⟨q - 1, by omega⟩ = j₀ ∧ e ⟨q - 2, by omega⟩ = j₁ := by
  let last : Fin q := ⟨q - 1, by omega⟩
  let prev : Fin q := ⟨q - 2, by omega⟩
  obtain ⟨e₁, he₁⟩ := exists_equiv_fin_last hcard (by omega : 0 < q) j₀
  have hlp : last ≠ prev := by intro h; have := congrArg Fin.val h; dsimp [last, prev] at this; omega
  have hlk : last ≠ e₁.symm j₁ := by
    intro h
    have h' := congrArg e₁ h
    simp only [Equiv.apply_symm_apply] at h'
    exact hne (he₁.symm.trans h')
  refine ⟨(Equiv.swap prev (e₁.symm j₁)).trans e₁, ?_, ?_⟩
  · change e₁ ((Equiv.swap prev (e₁.symm j₁)) last) = j₀
    rw [Equiv.swap_apply_of_ne_of_ne hlp hlk]
    exact he₁
  · change e₁ ((Equiv.swap prev (e₁.symm j₁)) prev) = j₁
    rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_ne_mem_zero_sum (a : ι → ℤ) (ha : ∀ i, a i ≠ 0)
    (I : Finset ι) (hI : ∑ i ∈ I, a i = 0) (p : ι) (hp : p ∈ I) :
    ∃ j ∈ I, j ≠ p := by
  have hcard : 1 < I.card := by
    by_contra h
    have hsing : I = {p} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hp, fun j hj => (Finset.card_le_one.mp (by omega : I.card ≤ 1)) j hj p hp⟩
    rw [hsing, Finset.sum_singleton] at hI
    exact ha p hI
  exact Finset.exists_ne_of_one_lt_card hcard p

theorem card_nonpivot {s : ℕ} (p : Fin s) :
    Fintype.card {i : Fin s // i ≠ p} = s - 1 := by
  rw [Fintype.card_subtype_compl (fun i : Fin s => i = p), Fintype.card_subtype_eq,
    Fintype.card_fin]

omit [DecidableEq ι] in
theorem exists_matrix_entry_bound {κ : Type*} [Fintype κ] (B : Matrix ι κ ℤ) :
    ∃ p : ℕ, 0 < p ∧ ∀ i j, |B i j| ≤ (p : ℤ) := by
  let p := max 1 (Finset.univ.sup (fun ij : ι × κ => (B ij.1 ij.2).natAbs))
  refine ⟨p, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro i j
  have h := (Finset.le_sup (f := fun ij : ι × κ => (B ij.1 ij.2).natAbs)
    (Finset.mem_univ (i, j))).trans (le_max_right 1 _)
  change (B i j).natAbs ≤ p at h
  have h' : ((B i j).natAbs : ℤ) ≤ p := by exact_mod_cast h
  simpa only [Int.natCast_natAbs] using h'

/-- The kernel has an injective integral parametrization with one common positive row leader. -/
theorem exists_common_leading_kernel {s : ℕ} (hs : 2 ≤ s) (a : Fin s → ℤ)
    (ha : ∀ i, a i ≠ 0) (I : Finset (Fin s)) (hIne : I.Nonempty)
    (hI : ∑ i ∈ I, a i = 0) :
    ∃ c : ℕ, 0 < c ∧ ∃ B : Matrix (Fin s) (Fin (s - 1)) ℤ,
      Function.Injective B.mulVec ∧
      (∀ y, (∑ i, a i * (B.mulVec y) i) = 0) ∧
      ∀ i, ∃ j, B i j = (c : ℤ) ∧ ∀ k, j < k → B i k = 0 := by
  obtain ⟨pivot, hpivot⟩ := hIne
  obtain ⟨j, hjI, hjp⟩ := exists_ne_mem_zero_sum a ha I hI pivot hpivot
  let J := {i : Fin s // i ≠ pivot}
  let j₀ : J := ⟨j, hjp⟩
  have hcard : Fintype.card J = s - 1 := card_nonpivot pivot
  have hq : 0 < s - 1 := by omega
  let last : Fin (s - 1) := ⟨s - 1 - 1, by omega⟩
  refine ⟨(a pivot).natAbs, Int.natAbs_pos.mpr (ha pivot), ?_⟩
  by_cases hfull : I = Finset.univ
  · let C := kernelColumns a pivot I j₀ none
    have hC : Function.Injective C.mulVec :=
      kernelColumns_injective a pivot I (ha pivot) j₀ hjI none (by simp)
    obtain ⟨e, he⟩ := exists_equiv_fin_last hcard hq j₀
    let B : Matrix (Fin s) (Fin (s - 1)) ℤ := C.submatrix id e
    refine ⟨B, mulVec_injective_reindex_columns C hC e, ?_, ?_⟩
    · apply matrix_weighted_sum_mulVec_eq_zero
      intro k
      exact kernelColumns_kernel a pivot I hI j₀ none (e k)
    · intro i
      refine ⟨last, ?_, ?_⟩
      · change C i (e last) = (a pivot).natAbs
        rw [he]
        simp only [C, kernelColumns, ↓reduceIte, insideSeed, hfull,
          Finset.mem_univ, ↓reduceIte, pivotScale]
      · intro k hk
        have hk' := k.isLt
        change last.val < k.val at hk
        dsimp [last] at hk
        omega
  · obtain ⟨i₁, hi₁⟩ : ∃ i : Fin s, i ∉ I := by
      by_contra! h
      exact hfull (Finset.eq_univ_iff_forall.mpr h)
    have hi₁p : i₁ ≠ pivot := by intro h; subst i₁; exact hi₁ hpivot
    let j₁ : J := ⟨i₁, hi₁p⟩
    have hj01 : j₀ ≠ j₁ := by
      intro h
      have h' : j = i₁ := congrArg Subtype.val h
      exact hi₁ (h' ▸ hjI)
    have hq₂ : 2 ≤ s - 1 := by
      have hJ := Fintype.one_lt_card_iff.mpr ⟨j₀, j₁, hj01⟩
      rw [hcard] at hJ
      omega
    let prev : Fin (s - 1) := ⟨s - 1 - 2, by omega⟩
    let C := kernelColumns a pivot I j₀ (some j₁)
    have hC : Function.Injective C.mulVec := by
      apply kernelColumns_injective a pivot I (ha pivot) j₀ hjI (some j₁)
      intro k hk
      have hk' : k = j₁ := Option.some.inj hk
      simpa only [hk'] using hi₁
    obtain ⟨e, he₀, he₁⟩ := exists_equiv_fin_last_two hcard hq₂ j₀ j₁ hj01
    let B : Matrix (Fin s) (Fin (s - 1)) ℤ := C.submatrix id e
    refine ⟨B, mulVec_injective_reindex_columns C hC e, ?_, ?_⟩
    · apply matrix_weighted_sum_mulVec_eq_zero
      intro k
      exact kernelColumns_kernel a pivot I hI j₀ (some j₁) (e k)
    · intro i
      by_cases hi : i ∈ I
      · refine ⟨last, ?_, ?_⟩
        · change C i (e last) = (a pivot).natAbs
          rw [he₀]
          simp only [C, kernelColumns, ↓reduceIte, insideSeed, if_pos hi, pivotScale]
        · intro k hk
          have hk' := k.isLt
          change last.val < k.val at hk
          dsimp [last] at hk
          omega
      · refine ⟨prev, ?_, ?_⟩
        · have hip : i ≠ pivot := by intro h; subst i; exact hi hpivot
          change C i (e prev) = (a pivot).natAbs
          rw [he₁]
          simp only [C, kernelColumns, if_neg (Ne.symm hj01), ↓reduceIte,
            outsideSeed_apply I hip, if_neg hi, pivotScale]
        · intro k hk
          have hklast : k = last := by
            apply Fin.ext
            have hk' := k.isLt
            change prev.val < k.val at hk
            dsimp [prev, last] at hk ⊢
            omega
          subst k
          change C i (e last) = 0
          rw [he₀]
          simp only [C, kernelColumns, ↓reduceIte, insideSeed, if_neg hi]

/-- A common-leading kernel matrix whose coordinates are all Deuber pattern entries. -/
theorem exists_deuber_kernel_matrix {s : ℕ} (hs : 2 ≤ s) (a : Fin s → ℤ)
    (ha : ∀ i, a i ≠ 0) (I : Finset (Fin s)) (hIne : I.Nonempty)
    (hI : ∑ i ∈ I, a i = 0) :
    ∃ p c : ℕ, 0 < p ∧ 0 < c ∧ ∃ B : Matrix (Fin s) (Fin (s - 1)) ℤ,
      Function.Injective B.mulVec ∧
      (∀ y, (∑ i, a i * (B.mulVec y) i) = 0) ∧
      (∀ y i, (B.mulVec y) i ∈ Deuber.pattern p (c : ℤ) y) := by
  obtain ⟨c, hc, B, hBinj, hBker, hBlead⟩ := exists_common_leading_kernel hs a ha I hIne hI
  obtain ⟨p, hp, hbound⟩ := exists_matrix_entry_bound B
  refine ⟨p, c, hp, hc, B, hBinj, hBker, ?_⟩
  intro y i
  obtain ⟨j, hj, hafter⟩ := hBlead i
  apply Deuber.row_subset_pattern p (c : ℤ) y j
  apply Deuber.sum_mem_row_of_coefficients hj _ hafter
  intro k _
  exact abs_le.mp (hbound i k)

end Sidon.QuantitativeRado
