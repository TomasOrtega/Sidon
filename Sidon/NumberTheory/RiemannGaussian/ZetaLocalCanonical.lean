/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.ZetaLocalDiscBounds

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem analyticOnNhd_localZetaPoleRemoved_unitDisc (y : ℝ) :
    AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 (1 : ℝ)) :=
  fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z

theorem localZetaPoleRemoved_zero_ne_zero (y : ℝ) : localZetaPoleRemoved y 0 ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (sixteenth_le_norm_localZetaPoleRemoved_zero y)))

theorem meromorphicOrderAt_localZetaPoleRemoved_ne_top (y : ℝ) {z : ℂ}
    (hz : z ∈ closedBall 0 (1 : ℝ)) : meromorphicOrderAt (localZetaPoleRemoved y) z ≠ ⊤ := by
  let f := localZetaPoleRemoved y
  let CB : Set ℂ := closedBall 0 (1 : ℝ)
  have han := analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have hzero : (0 : ℂ) ∈ CB := by simp [CB]
  have horder : meromorphicOrderAt f 0 = 0 :=
    (han 0 hzero).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr (localZetaPoleRemoved_zero_ne_zero y)
  have hconnected : IsConnected CB :=
    ⟨nonempty_closedBall.mpr (by norm_num), (convex_closedBall (0 : ℂ) 1).isPreconnected⟩
  have hall := (han.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hconnected).mp
    ⟨⟨0, hzero⟩, by simp [f, horder]⟩
  exact hall ⟨z, hz⟩

theorem exists_localZetaSphere_zeroFree (y : ℝ) : ∃ R : ℝ,
    3 / 4 < R ∧ R < 7 / 8 ∧ ∀ z : ℂ, ‖z‖ = R → localZetaPoleRemoved y z ≠ 0 := by
  let f := localZetaPoleRemoved y
  let CB : Set ℂ := closedBall 0 (1 : ℝ)
  have han := analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have horders : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤ :=
    fun u ↦ meromorphicOrderAt_localZetaPoleRemoved_ne_top y u.property
  have hzeros : (CB ∩ f ⁻¹' {0}).Finite := by
    rw [han.meromorphicNFOn.zero_set_eq_divisor_support horders]
    exact (divisor f CB).finiteSupport (isCompact_closedBall 0 1)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite (by norm_num : (3 / 4 : ℝ) < 7 / 8)) (bad.finite_toSet.subset h)
  obtain ⟨R, hR, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR.1, hR.2, fun z hz hzero ↦ ?_⟩
  apply hbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall, dist_zero_right, hz]
  linarith [hR.2]

def localZetaCanonicalRadius (y : ℝ) : ℝ := Classical.choose (exists_localZetaSphere_zeroFree y)

theorem localZetaCanonicalRadius_spec (y : ℝ) :
    3 / 4 < localZetaCanonicalRadius y ∧ localZetaCanonicalRadius y < 7 / 8 ∧
      ∀ z : ℂ, ‖z‖ = localZetaCanonicalRadius y → localZetaPoleRemoved y z ≠ 0 :=
  Classical.choose_spec (exists_localZetaSphere_zeroFree y)

theorem localZetaCanonicalRadius_pos (y : ℝ) : 0 < localZetaCanonicalRadius y :=
  (by norm_num : (0 : ℝ) < 3 / 4).trans (localZetaCanonicalRadius_spec y).1

theorem analyticOnNhd_localZetaPoleRemoved_canonicalDisc (y : ℝ) :
    AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 (localZetaCanonicalRadius y)) :=
  fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z

theorem divisor_localZetaPoleRemoved_sphere_eq_zero (y : ℝ) :
    divisor (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) = 0 := by
  have han : AnalyticOnNhd ℂ (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) :=
    fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) (localZetaCanonicalRadius y)
  · have hfz := (localZetaCanonicalRadius_spec y).2.2 z
      (by simpa only [mem_sphere, dist_zero_right] using hz)
    have ho : meromorphicOrderAt (localZetaPoleRemoved y) z = 0 :=
      (han z hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
    rw [han.meromorphicOn.divisor_apply hz]
    simp [ho]
  · change (if MeromorphicOn (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) ∧
        z ∈ sphere 0 (localZetaCanonicalRadius y) then _ else 0) = 0
    rw [ite_eq_right (fun h ↦ hz h.2)]

theorem exists_localZetaECanonicalDecomp (y : ℝ) : ∃ g : ℂ → ℂ,
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) g (localZetaCanonicalRadius y) := by
  apply MeromorphicOn.exists_ecanonicalDecomp
    (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).meromorphicOn
  intro z
  apply meromorphicOrderAt_localZetaPoleRemoved_ne_top y
  exact (closedBall_subset_closedBall (by linarith [(localZetaCanonicalRadius_spec y).2.1])) z.property

def localZetaCanonicalResidual (y : ℝ) : ℂ → ℂ := Classical.choose (exists_localZetaECanonicalDecomp y)

theorem localZetaCanonicalResidual_decomp (y : ℝ) :
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) (localZetaCanonicalResidual y) (localZetaCanonicalRadius y) :=
  Classical.choose_spec (exists_localZetaECanonicalDecomp y)

end

end RiemannGaussian
