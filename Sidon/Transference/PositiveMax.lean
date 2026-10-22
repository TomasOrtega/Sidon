import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Positive maxima and their polynomial approximation -/

noncomputable section

namespace Sidon

variable {ι : Type*} [Fintype ι]

def positiveMax (t : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Option ι => i.elim 0 t

theorem positiveMax_nonneg (t : ι → ℝ) : 0 ≤ positiveMax t :=
  Finset.le_sup' (fun i : Option ι => i.elim 0 t) (Finset.mem_univ none)

theorem le_positiveMax (t : ι → ℝ) (i : ι) : t i ≤ positiveMax t :=
  Finset.le_sup' (fun i : Option ι => i.elim 0 t) (Finset.mem_univ (some i))

theorem positiveMax_le {t : ι → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : ∀ i, t i ≤ L) :
    positiveMax t ≤ L := by
  apply Finset.sup'_le
  intro i _
  cases i with
  | none => exact hL
  | some i => exact h i

theorem exists_positiveMax_eq (t : ι → ℝ) :
    ∃ i : Option ι, positiveMax t = i.elim 0 t := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : Option ι => i.elim 0 t)
  exact ⟨i, hi⟩

theorem continuous_positiveMax : Continuous (positiveMax (ι := ι)) := by
  have h := Continuous.finset_sup' (s := (Finset.univ : Finset (Option ι)))
    (f := fun i t => i.elim (0 : ℝ) t) Finset.univ_nonempty (by
      intro i _
      cases i with
      | none => exact continuous_const
      | some i => exact continuous_apply i)
  convert h using 1
  funext t
  exact (Finset.sup'_apply Finset.univ_nonempty (fun (i : Option ι) (t : ι → ℝ) => i.elim (0 : ℝ) t) t).symm

private def cubeCoordinate (L : ℝ) (i : ι) : C((ι → Set.Icc (-L) L), ℝ) where
  toFun x := (x i).val
  continuous_toFun := continuous_subtype_val.comp (continuous_apply i)

omit [Fintype ι] in
private theorem eval_cubeCoordinate (L : ℝ) (P : MvPolynomial ι ℝ)
    (x : ι → Set.Icc (-L) L) :
    (MvPolynomial.aeval (cubeCoordinate L) P) x = MvPolynomial.aeval (fun i => (x i).val) P := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (MvPolynomial.aeval (cubeCoordinate L)) =
      MvPolynomial.aeval (fun i => (x i).val) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [cubeCoordinate]
  exact AlgHom.congr_fun h P

/-- The polynomial and all its coefficients are chosen before any interval length `N`. -/
theorem exists_polynomial_positiveMax (L : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ P : MvPolynomial ι ℝ, ∀ t : ι → ℝ, (∀ i, |t i| ≤ L) →
      |MvPolynomial.aeval t P - positiveMax t| < τ := by
  let A := (MvPolynomial.aeval (R := ℝ) (cubeCoordinate (ι := ι) L)).range
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hi : ∃ i, (x i).val ≠ (y i).val := by
      by_contra h
      apply hxy
      funext i
      exact Subtype.ext (not_ne_iff.mp (not_exists.mp h i))
    obtain ⟨i, hi⟩ := hi
    refine ⟨cubeCoordinate L i, ⟨cubeCoordinate L i, ?_, rfl⟩, hi⟩
    exact ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩
  let M : (ι → Set.Icc (-L) L) → ℝ := fun x => positiveMax (fun i => (x i).val)
  have hM : Continuous M := continuous_positiveMax.comp (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i))
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    A hsep M hM τ hτ
  obtain ⟨P, hP⟩ := g.property
  refine ⟨P, fun t ht => ?_⟩
  let x : ι → Set.Icc (-L) L := fun i => ⟨t i, abs_le.mp (ht i)⟩
  have hx := hg x
  rw [← hP] at hx
  change ‖(MvPolynomial.aeval (cubeCoordinate L) P) x - M x‖ < τ at hx
  rw [eval_cubeCoordinate] at hx
  exact hx

end Sidon
