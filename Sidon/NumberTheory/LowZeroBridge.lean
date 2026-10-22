import Sidon.NumberTheory.ZetaZeroCount
import Sidon.NumberTheory.RiemannGaussian.EtaZetaPrimeProduct

/-! Comparing both signs of the actual zero spectrum to positive-height occurrences. -/

noncomputable section

open RiemannGaussian
open scoped BigOperators

namespace Sidon

def boundedNontrivialZeros (T : ℝ) : Finset NontrivialZetaZero := by
  classical
  exact ((isCompact_closedBall (0 : ℂ) T).inter_nontrivialZetaZeroSet_finite.toFinset).subtype
    IsNontrivialZetaZero

@[simp] theorem mem_boundedNontrivialZeros {T : ℝ} {ρ : NontrivialZetaZero} :
    ρ ∈ boundedNontrivialZeros T ↔ ‖(ρ : ℂ)‖ ≤ T := by
  classical
  simp [boundedNontrivialZeros, Set.Finite.mem_toFinset, Metric.mem_closedBall,
    dist_zero_right, nontrivialZetaZeroSet]

def positiveNontrivialZeros (T : ℝ) : Finset NontrivialZetaZero := by
  classical
  exact (criticalZetaZeros T).subtype IsNontrivialZetaZero

@[simp] theorem mem_positiveNontrivialZeros {T : ℝ} {ρ : NontrivialZetaZero} :
    ρ ∈ positiveNontrivialZeros T ↔ 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T := by
  classical
  simp only [positiveNontrivialZeros, Finset.mem_subtype, mem_criticalZetaZeros]
  simp only [ρ.property.1, (NontrivialZetaZero.zero_lt_re ρ).le,
    (NontrivialZetaZero.re_lt_one ρ).le, true_and]

theorem isNontrivialZetaZero_of_mem_critical {T : ℝ} {z : ℂ}
    (hz : z ∈ criticalZetaZeros T) : IsNontrivialZetaZero z := by
  obtain ⟨hzero, _, _, him, _⟩ := mem_criticalZetaZeros.mp hz
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    simp at him
  · intro hz1
    subst z
    simp at him

theorem sum_positiveNontrivialZeros (T : ℝ) (f : ℂ → ℝ) :
    (∑ ρ ∈ positiveNontrivialZeros T, (analyticZetaZeroMultiplicity ρ : ℝ) * f (ρ : ℂ)) =
      ∑ z ∈ zetaZeroOccurrences T, f z.1 := by
  classical
  rw [sum_zetaZeroOccurrences]
  apply Finset.sum_bij (fun (ρ : NontrivialZetaZero) _ => (ρ : ℂ))
  · intro ρ hρ
    exact Finset.mem_subtype.mp hρ
  · intro ρ _ σ _ hρσ
    exact Subtype.ext hρσ
  · intro z hz
    let ρ : NontrivialZetaZero := ⟨z, isNontrivialZetaZero_of_mem_critical hz⟩
    exact ⟨ρ, Finset.mem_subtype.mpr hz, rfl⟩
  · intro ρ _
    rfl

theorem boundedNontrivialZeros_subset_positive_conjugates (T : ℝ) :
    boundedNontrivialZeros T ⊆ positiveNontrivialZeros T ∪
      (positiveNontrivialZeros T).image NontrivialZetaZero.conjugate := by
  classical
  intro ρ hρ
  have hnorm : ‖(ρ : ℂ)‖ ≤ T := mem_boundedNontrivialZeros.mp hρ
  rcases lt_or_gt_of_ne (NontrivialZetaZero.im_ne_zero_of_eta_mass ρ) with hneg | hpos
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨NontrivialZetaZero.conjugate ρ, ?_, NontrivialZetaZero.conjugate_conjugate ρ⟩
    apply mem_positiveNontrivialZeros.mpr
    simp only [NontrivialZetaZero.conjugate_coe, Complex.conj_im]
    exact ⟨by linarith, (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans hnorm)⟩
  · apply Finset.mem_union_left
    exact mem_positiveNontrivialZeros.mpr ⟨hpos,
      (Complex.im_le_norm _).trans hnorm⟩


theorem sum_boundedNontrivialZeros_le_twice_occurrences (T : ℝ) (f : ℂ → ℝ)
    (hf : ∀ z, 0 ≤ f z) (hconj : ∀ z, f (starRingEnd ℂ z) = f z) :
    (∑ ρ ∈ boundedNontrivialZeros T,
      (analyticZetaZeroMultiplicity ρ : ℝ) * f (ρ : ℂ)) ≤
        2 * ∑ z ∈ zetaZeroOccurrences T, f z.1 := by
  classical
  let P := positiveNontrivialZeros T
  let w : NontrivialZetaZero → ℝ := fun ρ =>
    (analyticZetaZeroMultiplicity ρ : ℝ) * f (ρ : ℂ)
  have hd : Disjoint P (P.image NontrivialZetaZero.conjugate) := by
    apply Finset.disjoint_left.mpr
    intro ρ hρ himage
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp himage
    have hσpos := (mem_positiveNontrivialZeros.mp hσ).1
    have hρpos := (mem_positiveNontrivialZeros.mp hρ).1
    simp only [NontrivialZetaZero.conjugate_coe, Complex.conj_im] at hρpos
    linarith
  have hconjsum : (∑ ρ ∈ P.image NontrivialZetaZero.conjugate, w ρ) =
      ∑ ρ ∈ P, w ρ := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro ρ _
      simp only [w, analyticZetaZeroMultiplicity_conjugate,
        NontrivialZetaZero.conjugate_coe, hconj]
    · intro ρ _ σ _ heq
      have hh := congrArg NontrivialZetaZero.conjugate heq
      simpa only [NontrivialZetaZero.conjugate_conjugate] using hh
  calc
    _ ≤ ∑ ρ ∈ P ∪ P.image NontrivialZetaZero.conjugate, w ρ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (boundedNontrivialZeros_subset_positive_conjugates T)
        (fun ρ _ _ => mul_nonneg (Nat.cast_nonneg _) (hf _))
    _ = (∑ ρ ∈ P, w ρ) + ∑ ρ ∈ P.image NontrivialZetaZero.conjugate, w ρ :=
      Finset.sum_union hd
    _ = 2 * ∑ ρ ∈ P, w ρ := by rw [hconjsum]; ring
    _ = _ := by rw [sum_positiveNontrivialZeros]

end Sidon
