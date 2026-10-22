import Sidon.Transference.PolynomialMax

/-! # Compact convex sets for the colouring dense model -/

noncomputable section

open scoped Pointwise

namespace Sidon

namespace FourierSpace

variable {N r : ℕ}

def coordinate (x : Fin N) : FourierSpace N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Pi.evalAlgHom ℝ (fun _ : Fin N => ℝ) x).toLinearMap

@[simp] theorem coordinate_apply (x : Fin N) (f : FourierSpace N) : coordinate x f = f x := rfl

theorem eq_sum_delta (f : FourierSpace N) : f = ∑ x : Fin N, (f x) • delta x := by
  funext y
  rw [Finset.sum_apply]
  change f y = ∑ x : Fin N, f x * (if x = y then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem functional_eq_sum (L : FourierSpace N →L[ℝ] ℝ) (f : FourierSpace N) :
    L f = ∑ x : Fin N, f x * L (delta x) := by
  conv_lhs => rw [eq_sum_delta f]
  simp only [map_sum, map_smul, smul_eq_mul]

abbrev ColourTuple (N r : ℕ) := Fin r → FourierSpace N

def models (N r : ℕ) : Set (ColourTuple N r) :=
  {g | (∀ i x, 0 ≤ g i x) ∧ ∀ x, ∑ i : Fin r, g i x ≤ 1}

theorem zero_mem_models : (0 : ColourTuple N r) ∈ models N r := by
  constructor
  · intro i x; rfl
  · intro x
    change (∑ i : Fin r, (0 : ℝ)) ≤ 1
    simp

theorem models_coordinate_le_one {g : ColourTuple N r} (hg : g ∈ models N r)
    (i : Fin r) (x : Fin N) : g i x ≤ 1 := by
  exact (Finset.single_le_sum (fun j _ => hg.1 j x) (Finset.mem_univ i)).trans (hg.2 x)

theorem models_norm_le {g : ColourTuple N r} (hg : g ∈ models N r) : ‖g‖ ≤ (N : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg N)).mpr
  intro i
  calc
    ‖g i‖ ≤ ∑ x : Fin N, g i x := norm_nonneg_le_sum (hg.1 i)
    _ ≤ ∑ _ : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun x _ => models_coordinate_le_one hg i x)
    _ = _ := by simp

theorem isClosed_models (N r : ℕ) : IsClosed (models N r) := by
  change IsClosed ({g : ColourTuple N r | ∀ i x, 0 ≤ g i x} ∩
    {g | ∀ x, ∑ i : Fin r, g i x ≤ 1})
  simp_rw [Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const ((coordinate x).continuous.comp (continuous_apply i))
  · apply isClosed_iInter
    intro x
    exact isClosed_le (continuous_finset_sum _ fun i _ =>
      (coordinate x).continuous.comp (continuous_apply i)) continuous_const

theorem isCompact_models (N r : ℕ) : IsCompact (models N r) := by
  apply (isCompact_closedBall (0 : ColourTuple N r) (N : ℝ)).of_isClosed_subset (isClosed_models N r)
  intro g hg
  simpa only [Metric.mem_closedBall, dist_zero_right] using models_norm_le hg

theorem convex_models (N r : ℕ) : Convex ℝ (models N r) := by
  intro f hf g hg a b ha hb hab
  constructor
  · intro i x
    change 0 ≤ a * f i x + b * g i x
    exact add_nonneg (mul_nonneg ha (hf.1 i x)) (mul_nonneg hb (hg.1 i x))
  · intro x
    change (∑ i : Fin r, (a * f i x + b * g i x)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left (hf.2 x) ha
    have h₂ := mul_le_mul_of_nonneg_left (hg.2 x) hb
    nlinarith

def tuplePairing (φ u : ColourTuple N r) : ℝ := ∑ i : Fin r, pairing (φ i) (u i)

theorem tuplePairing_eq_sum (φ u : ColourTuple N r) :
    tuplePairing φ u = ∑ x : Fin N, ∑ i : Fin r, u i x * φ i x := by
  unfold tuplePairing
  simp only [pairing_apply]
  exact Finset.sum_comm

def representingTuple (L : ColourTuple N r →L[ℝ] ℝ) : ColourTuple N r :=
  fun i x => L (Pi.single i (delta x))

theorem functional_eq_tuplePairing (L : ColourTuple N r →L[ℝ] ℝ) (u : ColourTuple N r) :
    L u = tuplePairing (representingTuple L) u := by
  have hu : u = ∑ i : Fin r, Pi.single i (u i) := by
    funext i
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, if_true]
  conv_lhs => rw [hu, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  let Li : FourierSpace N →L[ℝ] ℝ := L.comp
    (LinearMap.toContinuousLinearMap (LinearMap.single ℝ (fun _ : Fin r => FourierSpace N) i))
  exact functional_eq_sum Li (u i)

/-- The pointwise positive maximum is the support function of the model simplex. -/
theorem exists_models_pairing_positiveMax (φ : ColourTuple N r) :
    ∃ g ∈ models N r, tuplePairing φ g = ∑ x : Fin N, positiveMax (fun i => φ i x) := by
  choose winner hw using fun x : Fin N => exists_positiveMax_eq (fun i => φ i x)
  let g : ColourTuple N r := fun i x => if winner x = some i then 1 else 0
  refine ⟨g, ?_, ?_⟩
  · constructor
    · intro i x
      change 0 ≤ if winner x = some i then (1 : ℝ) else 0
      split_ifs <;> norm_num
    · intro x
      change (∑ i : Fin r, if winner x = some i then (1 : ℝ) else 0) ≤ 1
      cases hx : winner x with
      | none => simp [hx]
      | some j => simp [hx, eq_comm]
  · rw [tuplePairing_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    change (∑ i : Fin r, (if winner x = some i then (1 : ℝ) else 0) * φ i x) = _
    rw [hw x]
    cases hx : winner x with
    | none => simp [hx]
    | some j => simp [hx, eq_comm]

/-- Strict separation, expressed using the coordinate pairing. -/
theorem separate_models_thickening {q : ℝ} (v : ColourTuple N r)
    (hv : v ∉ models N r + Metric.closedBall 0 q) :
    ∃ φ : ColourTuple N r, ∀ g ∈ models N r, ∀ h : ColourTuple N r,
      ‖h‖ ≤ q → tuplePairing φ (g + h) < tuplePairing φ v := by
  obtain ⟨L, c, hLc, hc⟩ := geometric_hahn_banach_closed_point
    ((convex_models N r).add (convex_closedBall 0 q))
    (((isCompact_models N r).add (isCompact_closedBall 0 q)).isClosed) hv
  refine ⟨representingTuple L, fun g hg h hh => ?_⟩
  rw [← functional_eq_tuplePairing, ← functional_eq_tuplePairing]
  apply (hLc _ ?_).trans hc
  exact ⟨g, hg, h, by simpa only [Metric.mem_closedBall, dist_zero_right] using hh, rfl⟩


theorem strict_separation {K : Set (FourierSpace N)} (hKc : Convex ℝ K) (hK : IsClosed K)
    {v : FourierSpace N} (hv : v ∉ K) :
    ∃ φ : FourierSpace N, ∀ u ∈ K, pairing φ u < pairing φ v := by
  obtain ⟨L, a, ha, hav⟩ := geometric_hahn_banach_closed_point hKc hK hv
  refine ⟨fun x => L (delta x), fun u hu => ?_⟩
  change (∑ x : Fin N, u x * L (delta x)) < ∑ x : Fin N, v x * L (delta x)
  rw [← functional_eq_sum, ← functional_eq_sum]
  exact (ha u hu).trans hav

end FourierSpace

end Sidon
