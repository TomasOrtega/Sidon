module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic

@[expose] public section

/-! # Interpolation of vertical square integrals -/

noncomputable section

open Set MeasureTheory Complex Complex.HadamardThreeLines
open scoped Topology

namespace Sidon

theorem continuousOn_compact_integral {S : Set ℂ} (hS : IsClosed S)
    {K : Set ℝ} (hK : IsCompact K) {F : ℂ → ℝ → ℂ}
    (hF : ContinuousOn F.uncurry (S ×ˢ univ)) :
    ContinuousOn (fun z => ∫ t in K, F z t) S := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  have hc : Continuous (fun p : S × ℝ => F p.1.val p.2) := by
    change Continuous (F.uncurry ∘ (fun p : S × ℝ => (p.1.val, p.2)))
    exact hF.comp_continuous (by fun_prop)
      (fun p => ⟨p.1.property, mem_univ _⟩)
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun x : S => fun t : ℝ => F x.val t) hc hK
  exact continuousOn_iff_continuous_domRestrict.mpr hi

theorem differentiableOn_compact_integral {U : Set ℂ} (hU : IsOpen U)
    {K : Set ℝ} (hK : IsCompact K) {F F' : ℂ → ℝ → ℂ}
    (hF : ContinuousOn F.uncurry (U ×ˢ univ))
    (hF' : ContinuousOn F'.uncurry (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t ∈ K, HasDerivAt (fun w => F w t) (F' z t) z) :
    DifferentiableOn ℂ (fun z => ∫ t in K, F z t) U := by
  intro z hz
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (F w) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw, mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (F' w) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw, mem_univ t⟩)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  have hcp := (isCompact_closedBall z r).prod hK
  have hcont : ContinuousOn F'.uncurry (Metric.closedBall z r ×ˢ K) := by
    apply hF'.mono
    intro p hp
    exact ⟨hball hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcp.bddAbove_image hcont.norm
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := F) (F' := F') (bound := fun _ => M)
    (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.mono (hU.mem_nhds hz) (fun w hw => (hc w hw).aestronglyMeasurable))
    ((hc z hz).continuousOn.integrableOn_compact hK)
    (hc' z hz).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
      intro w hw
      exact hM (show ‖F' w t‖ ∈ (fun p : ℂ × ℝ => ‖F' p.1 p.2‖) ''
        (Metric.closedBall z r ×ˢ K) from
        ⟨(w, t), ⟨Metric.mem_closedBall.mpr hw.le, ht⟩, rfl⟩))
    (integrableOn_const hK.measure_ne_top)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
      intro w hw
      exact hd w (hball (Metric.mem_closedBall.mpr hw.le)) t ht)
  exact hderiv.2.differentiableAt.differentiableWithinAt

def verticalPairing (Φ : ℂ → ℂ) (g : ℝ → ℂ) (c d : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc c d, Φ (z + (t : ℂ) * I) * star (g t)

theorem continuousOn_verticalPairing_integrand {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) :
    ContinuousOn (fun p : ℂ × ℝ => Φ (p.1 + (p.2 : ℂ) * I) * star (g p.2))
      (verticalClosedStrip a b ×ˢ univ) := by
  apply ContinuousOn.mul
  · apply hΦ.comp (by fun_prop)
    intro p hp
    simpa only [verticalClosedStrip, mem_preimage, add_re, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero] using hp.1
  · exact (continuous_star.comp (hg.comp continuous_snd)).continuousOn

theorem continuousOn_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    ContinuousOn (verticalPairing Φ g c d) (verticalClosedStrip a b) :=
  continuousOn_compact_integral (isClosed_Icc.preimage continuous_re) isCompact_Icc
    (continuousOn_verticalPairing_integrand hΦ hg)

theorem diffContOnCl_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    DiffContOnCl ℂ (verticalPairing Φ g c d) (verticalStrip a b) := by
  have hsub : verticalStrip a b ×ˢ (univ : Set ℝ) ⊆
      verticalClosedStrip a b ×ˢ univ := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  constructor
  · apply differentiableOn_compact_integral
      (F := fun z t => Φ (z + (t : ℂ) * I) * star (g t))
      (F' := fun z t => deriv Φ (z + (t : ℂ) * I) * star (g t))
      (isOpen_Ioo.preimage continuous_re) isCompact_Icc
      ((continuousOn_verticalPairing_integrand hΦ.continuousOn hg).mono hsub)
      ((continuousOn_verticalPairing_integrand hΦ.deriv.continuousOn hg).mono hsub)
    intro z hz t _
    have hzt : z + (t : ℂ) * I ∈ verticalClosedStrip a b := by
      simpa [verticalClosedStrip] using
        (show a ≤ z.re ∧ z.re ≤ b from ⟨hz.1.le, hz.2.le⟩)
    simpa using (((hΦ _ hzt).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).add_const ((t : ℂ) * I))).mul_const (star (g t))
  · have hcl : closure (verticalStrip a b) = verticalClosedStrip a b := by
      rw [verticalStrip, closure_preimage_re, closure_Ioo hab.ne]
      rfl
    rw [hcl]
    exact continuousOn_verticalPairing hΦ.continuousOn hg c d

theorem norm_compact_pairing_le {K : Set ℝ} (hK : IsCompact K) {f g : ℝ → ℂ}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hf₂ : Integrable (fun t => ‖f t‖ ^ 2)) :
    ‖∫ t in K, f t * star (g t)‖ ≤
      (∫ t : ℝ, ‖f t‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ t in K, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hfm : MemLp f 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable hK.measurableSet)).mpr
      (hf₂.mono_measure Measure.restrict_le_self)
  have hgm : MemLp g 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm (hg.aestronglyMeasurable hK.measurableSet)).mpr
      (hg.norm.pow 2 |>.integrableOn_compact hK)
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hfm)
    (by simpa only [ENNReal.ofReal_ofNat] using hgm)
  norm_num only [Real.rpow_two] at hholder
  calc
    _ ≤ ∫ t in K, ‖f t * star (g t)‖ := norm_integral_le_integral_norm _
    _ = ∫ t in K, ‖f t‖ * ‖g t‖ := by simp only [norm_mul, norm_star]
    _ ≤ _ := hholder
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow (integral_nonneg (fun t => sq_nonneg _))
          (setIntegral_le_integral hf₂ (Filter.Eventually.of_forall (fun t => sq_nonneg _)))
          (by norm_num)
      · positivity

def verticalL2 (Φ : ℂ → ℂ) (u : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2

theorem verticalL2_nonneg (Φ : ℂ → ℂ) (u : ℝ) : 0 ≤ verticalL2 Φ u :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem vertical_translate (z : ℂ) (t : ℝ) :
    z + (t : ℂ) * I = (z.re : ℂ) + ((z.im + t : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem integral_sq_vertical_translate (Φ : ℂ → ℂ) (z : ℂ) :
    (∫ t : ℝ, ‖Φ (z + (t : ℂ) * I)‖ ^ 2) = verticalL2 Φ z.re := by
  have heq : (fun t : ℝ => ‖Φ (z + (t : ℂ) * I)‖ ^ 2) =
      (fun t : ℝ => ‖Φ ((z.re : ℂ) + ((z.im + t : ℝ) : ℂ) * I)‖ ^ 2) := by
    funext t
    rw [vertical_translate z t]
  rw [heq]
  exact integral_add_left_eq_self (μ := volume)
    (fun t : ℝ => ‖Φ ((z.re : ℂ) + (t : ℂ) * I)‖ ^ 2) z.im

theorem norm_verticalPairing_le {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip a b) :
    ‖verticalPairing Φ g c d z‖ ≤ (verticalL2 Φ z.re) ^ (1 / 2 : ℝ) *
      (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hc : Continuous (fun t : ℝ => Φ (z + (t : ℂ) * I)) := by
    apply hΦ.comp_continuous (by fun_prop)
    intro t
    simpa [verticalClosedStrip] using hz
  have hi : Integrable (fun t : ℝ => ‖Φ (z + (t : ℂ) * I)‖ ^ 2) := by
    convert (hsq z.re hz).comp_add_left z.im using 1
    funext t
    rw [vertical_translate z t]
  have hh := norm_compact_pairing_le (K := Icc c d) isCompact_Icc
    hc.continuousOn hg.continuousOn hi
  rw [integral_sq_vertical_translate] at hh
  exact hh

theorem bddAbove_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    BddAbove ((norm ∘ verticalPairing Φ g c d) '' verticalClosedStrip a b) := by
  obtain ⟨M, hM⟩ := hΦ
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image (hg.norm.continuousOn :
    ContinuousOn (fun t => ‖g t‖) (Icc c d))
  refine ⟨(max M 0 * max G 0) * volume.real (Icc c d), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t ht
  rw [norm_mul, norm_star]
  apply mul_le_mul
  · apply (hM ?_).trans (le_max_left _ _)
    refine ⟨z + (t : ℂ) * I, ?_, rfl⟩
    simpa [verticalClosedStrip] using hz
  · exact (hG (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · positivity
  · positivity

theorem norm_verticalPairing_interpolate {Φ : ℂ → ℂ} {a b σ A B : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : verticalL2 Φ a ≤ A ^ 2) (hright : verticalL2 Φ b ≤ B ^ 2)
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    ‖verticalPairing Φ g c d (σ : ℂ)‖ ≤
      (A * (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ)) ^
          (1 - (σ - a) / (b - a)) *
      (B * (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ)) ^
          ((σ - a) / (b - a)) := by
  apply norm_le_interp_of_mem_verticalClosedStrip' hab hσ
    (diffContOnCl_verticalPairing hab hΦ hg c d)
    (bddAbove_verticalPairing hbound hg c d)
  · intro z hz
    have hh := norm_verticalPairing_le hΦ.continuousOn hsq hg c d
      (z := z) (by simpa only [verticalClosedStrip, mem_preimage, mem_Icc] using
        (show a ≤ z.re ∧ z.re ≤ b from
        ⟨le_of_eq hz.symm, (le_of_eq hz).trans hab.le⟩))
    change z.re = a at hz
    rw [hz] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg
      (fun t => sq_nonneg _)) _)
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left hA).mpr hleft
  · intro z hz
    have hh := norm_verticalPairing_le hΦ.continuousOn hsq hg c d
      (z := z) (by simpa only [verticalClosedStrip, mem_preimage, mem_Icc] using
        (show a ≤ z.re ∧ z.re ≤ b from
        ⟨hab.le.trans (le_of_eq hz.symm), le_of_eq hz⟩))
    change z.re = b at hz
    rw [hz] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg
      (fun t => sq_nonneg _)) _)
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left hB).mpr hright

theorem self_test_interpolation {J A B θ : ℝ} (hJ : 0 ≤ J) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : J ≤ (A * J ^ (1 / 2 : ℝ)) ^ (1 - θ) *
      (B * J ^ (1 / 2 : ℝ)) ^ θ) :
    J ≤ (A ^ (1 - θ) * B ^ θ) ^ 2 := by
  by_cases hzero : J = 0
  · rw [hzero]
    positivity
  have hpos : 0 < Real.sqrt J := Real.sqrt_pos.mpr (lt_of_le_of_ne hJ (Ne.symm hzero))
  have hsq := Real.sq_sqrt hJ
  rw [← Real.sqrt_eq_rpow] at h
  have hfactor : (A * Real.sqrt J) ^ (1 - θ) * (B * Real.sqrt J) ^ θ =
      (A ^ (1 - θ) * B ^ θ) * Real.sqrt J := by
    rw [Real.mul_rpow hA hpos.le, Real.mul_rpow hB hpos.le]
    calc
      _ = (A ^ (1 - θ) * B ^ θ) *
          (Real.sqrt J ^ (1 - θ) * Real.sqrt J ^ θ) := by ring
      _ = _ := by rw [← Real.rpow_add hpos]; simp
  rw [hfactor] at h
  have hroot : Real.sqrt J ≤ A ^ (1 - θ) * B ^ θ := by nlinarith
  have hC : 0 ≤ A ^ (1 - θ) * B ^ θ := by positivity
  nlinarith

theorem verticalPairing_self (Φ : ℂ → ℂ) (σ c d : ℝ) :
    ‖verticalPairing Φ (fun t => Φ ((σ : ℂ) + (t : ℂ) * I)) c d (σ : ℂ)‖ =
      ∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have heq : verticalPairing Φ (fun t => Φ ((σ : ℂ) + (t : ℂ) * I)) c d (σ : ℂ) =
      Complex.ofReal (∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
    unfold verticalPairing
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Compact self-pairings and exhaustion prove the vertical square-integral bound. -/
theorem verticalL2_le_interpolation {Φ : ℂ → ℂ} {a b σ A B : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : verticalL2 Φ a ≤ A ^ 2) (hright : verticalL2 Φ b ≤ B ^ 2) :
    verticalL2 Φ σ ≤
      (A ^ (1 - (σ - a) / (b - a)) * B ^ ((σ - a) / (b - a))) ^ 2 := by
  have hc : Continuous (fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * I)) := by
    apply hΦ.continuousOn.comp_continuous (by fun_prop)
    intro t
    simpa [verticalClosedStrip] using hσ
  have hfinite (c d : ℝ) : (∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (A ^ (1 - (σ - a) / (b - a)) * B ^ ((σ - a) / (b - a))) ^ 2 := by
    have hh := norm_verticalPairing_interpolate hab hσ hΦ hbound hsq
      hA hB hleft hright hc c d
    rw [verticalPairing_self] at hh
    exact self_test_interpolation (integral_nonneg (fun _ => sq_nonneg _)) hA hB hh
  have hmono : Monotone (fun L : ℝ => Icc (-L) L) := by
    intro L M hLM
    exact Icc_subset_Icc (neg_le_neg hLM) hLM
  have hunion : (⋃ L : ℝ, Icc (-L) L) = univ := by
    apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr ⟨|t|, neg_abs_le t, le_abs_self t⟩
  have ht := tendsto_setIntegral_of_monotone
    (μ := volume) (f := fun t : ℝ => ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (fun L : ℝ => measurableSet_Icc) hmono
    (by rw [hunion]; simpa using hsq σ hσ)
  have hlim : Filter.Tendsto
      (fun L : ℝ => ∫ t in Icc (-L) L, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      Filter.atTop (𝓝 (verticalL2 Φ σ)) := by
    simpa only [hunion, Measure.restrict_univ, verticalL2] using ht
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun L => hfinite (-L) L))

/-- The vertical square integral of a bounded analytic function is logarithmically convex. -/
theorem verticalL2_logConvex {Φ : ℂ → ℂ} {a b σ : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2)) :
    verticalL2 Φ σ ≤
      verticalL2 Φ a ^ (1 - (σ - a) / (b - a)) *
        verticalL2 Φ b ^ ((σ - a) / (b - a)) := by
  have hJa := verticalL2_nonneg Φ a
  have hJb := verticalL2_nonneg Φ b
  have hh := verticalL2_le_interpolation hab hσ hΦ hbound hsq
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (le_of_eq (Real.sq_sqrt hJa).symm) (le_of_eq (Real.sq_sqrt hJb).symm)
  rw [mul_pow, Real.rpow_pow_comm (Real.sqrt_nonneg _),
    Real.rpow_pow_comm (Real.sqrt_nonneg _), Real.sq_sqrt hJa, Real.sq_sqrt hJb] at hh
  exact hh

end Sidon
