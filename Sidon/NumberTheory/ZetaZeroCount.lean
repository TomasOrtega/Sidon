import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! # Finite zeta-zero counts with analytic multiplicity -/

noncomputable section

open Filter
open scoped Topology

namespace Sidon

/-- Zeta zeros in the closed critical strip at positive height at most `T`. -/
def criticalZetaZeros (T : ℝ) : Finset ℂ :=
  ((isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_riemannZetaZeros_finite.toFinset).filter
    fun ρ => 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T

theorem mem_criticalZetaZeros {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalZetaZeros T ↔
      riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  classical
  simp only [criticalZetaZeros, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, mem_riemannZetaZeros]
  constructor
  · rintro ⟨⟨_, hz⟩, hρ⟩
    exact ⟨hz, hρ⟩
  · rintro ⟨hz, hρ⟩
    refine ⟨⟨?_, hz⟩, hρ⟩
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ |T| + 2 := by
        rw [abs_of_nonneg hρ.1, abs_of_nonneg hρ.2.2.1.le]
        linarith [le_abs_self T]

theorem analyticOrderAt_riemannZeta_ne_top (ρ : ℂ) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  intro htop
  have hzero : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z = 0 :=
    (analyticOrderAt_eq_top.mp htop).filter_mono nhdsWithin_le_nhds
  have hdisj := isClosed_and_discrete_iff.mp
    ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩ ρ
  have hnot : ∀ᶠ z in 𝓝[≠] ρ, z ∉ riemannZetaZeros :=
    Filter.disjoint_principal_right.mp hdisj
  obtain ⟨z, hnot, hz⟩ := (hnot.and hzero).exists
  exact hnot hz

theorem zeta_zero_multiplicity_pos {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    0 < analyticOrderNatAt riemannZeta ρ := by
  have hne : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_one_ne_zero hρ
  apply ENat.toNat_pos _ (analyticOrderAt_riemannZeta_ne_top ρ)
  exact analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hne, hρ⟩

/-- A zero of multiplicity `m` occurs once for each index in `Fin m`. -/
def zetaZeroOccurrences (T : ℝ) : Finset (ℂ × ℕ) :=
  (criticalZetaZeros T).biUnion fun ρ =>
    (Finset.range (analyticOrderNatAt riemannZeta ρ)).image fun k => (ρ, k)

theorem mem_zetaZeroOccurrences {T : ℝ} {ρ : ℂ} {k : ℕ} :
    (ρ, k) ∈ zetaZeroOccurrences T ↔
      ρ ∈ criticalZetaZeros T ∧ k < analyticOrderNatAt riemannZeta ρ := by
  classical
  simp only [zetaZeroOccurrences, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, j, hj, hρ, hk⟩
    subst z
    subst j
    exact ⟨hz, hj⟩
  · rintro ⟨hρ, hk⟩
    exact ⟨ρ, hρ, k, hk, rfl, rfl⟩

theorem sum_zetaZeroOccurrences (T : ℝ) (w : ℂ → ℝ) :
    (∑ z ∈ zetaZeroOccurrences T, w z.1) =
      ∑ ρ ∈ criticalZetaZeros T, (analyticOrderNatAt riemannZeta ρ : ℝ) * w ρ := by
  classical
  unfold zetaZeroOccurrences
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.sum_image]
    · simp
    · intro k _ l _ h
      exact (Prod.mk.inj h).2
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro z hzρ hzτ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hzρ
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hzτ
    exact hne (congrArg Prod.fst he).symm

theorem zetaZeroOccurrences_re_bounds {T : ℝ} {z : ℂ × ℕ}
    (hz : z ∈ zetaZeroOccurrences T) : 0 ≤ z.1.re ∧ z.1.re ≤ 1 := by
  have h := mem_criticalZetaZeros.mp (mem_zetaZeroOccurrences.mp hz).1
  exact ⟨h.2.1, h.2.2.1⟩

theorem zetaZeroOccurrences_height_bounds {T : ℝ} {z : ℂ × ℕ}
    (hz : z ∈ zetaZeroOccurrences T) : 0 < z.1.im ∧ z.1.im ≤ T := by
  have h := mem_criticalZetaZeros.mp (mem_zetaZeroOccurrences.mp hz).1
  exact h.2.2.2

/-- Multiplicity-sensitive `N(σ,T)` for positive imaginary parts. -/
def zetaZeroCount (σ T : ℝ) : ℕ :=
  ((zetaZeroOccurrences T).filter fun z => σ ≤ z.1.re).card

theorem zetaZeroCount_antitone (T : ℝ) : Antitone (fun σ => zetaZeroCount σ T) := by
  intro a b hab
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz, hb⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz, hab.trans hb⟩

theorem zetaZeroCount_mono_height (σ : ℝ) : Monotone (zetaZeroCount σ) := by
  intro T U hTU
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz, hσ⟩ := Finset.mem_filter.mp hz
  obtain ⟨hρ, hk⟩ := mem_zetaZeroOccurrences.mp hz
  obtain ⟨hzero, hre0, hre1, him0, himT⟩ := mem_criticalZetaZeros.mp hρ
  exact Finset.mem_filter.mpr ⟨mem_zetaZeroOccurrences.mpr
    ⟨mem_criticalZetaZeros.mpr ⟨hzero, hre0, hre1, him0, himT.trans hTU⟩, hk⟩, hσ⟩

theorem zetaZeroCount_le_low_add_high (σ T : ℝ) :
    zetaZeroCount σ T ≤ zetaZeroCount 0 4 +
      ((zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im)).card := by
  classical
  have hzero : (zetaZeroOccurrences 4).filter (fun z => 0 ≤ z.1.re) =
      zetaZeroOccurrences 4 := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    exact (zetaZeroOccurrences_re_bounds hz).1
  have hsub : (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re) ⊆
      zetaZeroOccurrences 4 ∪
        (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im) := by
    intro z hz
    obtain ⟨hz, hσ⟩ := Finset.mem_filter.mp hz
    by_cases hhigh : 4 ≤ z.1.im
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hσ, hhigh⟩)
    · apply Finset.mem_union_left
      obtain ⟨hρ, hk⟩ := mem_zetaZeroOccurrences.mp hz
      obtain ⟨hζ, hβ0, hβ1, hγ0, _⟩ := mem_criticalZetaZeros.mp hρ
      exact mem_zetaZeroOccurrences.mpr
        ⟨mem_criticalZetaZeros.mpr ⟨hζ, hβ0, hβ1, hγ0, (lt_of_not_ge hhigh).le⟩, hk⟩
  unfold zetaZeroCount
  rw [hzero]
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- A uniform estimate; its constant is independent of `σ` and `T`. -/
def UniformZetaZeroDensity (A : ℝ) (B : ℕ) (K T₀ : ℝ) : Prop :=
  ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
    (zetaZeroCount σ T : ℝ) ≤ K * T ^ (A * (1 - σ)) * (Real.log T) ^ B

/-- The width concerns every zero up to height `T`, including multiplicities. -/
def ZetaZeroFreeWidth (η : ℝ → ℝ) (T₀ : ℝ) : Prop :=
  ∀ T : ℝ, T₀ ≤ T → ∀ z ∈ zetaZeroOccurrences T, z.1.re ≤ 1 - η T

end Sidon
