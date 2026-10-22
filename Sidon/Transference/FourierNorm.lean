import Sidon.Analysis.FourierIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! # The real finite Fourier norm and its dual -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

/-- Real functions on the first `N` positive integers, with the Fourier supremum norm. -/
def FourierSpace (N : ℕ) := Fin N → ℝ

namespace FourierSpace

variable {N : ℕ}

instance : CommRing (FourierSpace N) := inferInstanceAs (CommRing (Fin N → ℝ))
instance : Algebra ℝ (FourierSpace N) := inferInstanceAs (Algebra ℝ (Fin N → ℝ))
instance : FiniteDimensional ℝ (FourierSpace N) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin N → ℝ))

def transform : FourierSpace N →ₗ[ℝ] C(AddCircle (1 : ℝ), ℂ) where
  toFun f := ∑ i : Fin N, (f i) • fourier ((i.val : ℤ) + 1)
  map_add' f g := by
    change (∑ i : Fin N, (f i + g i) • fourier (T := 1) ((i.val : ℤ) + 1)) = _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_smul (f i) (g i) (fourier (T := 1) ((i.val : ℤ) + 1)))
  map_smul' c f := by
    change (∑ i : Fin N, (c * f i) • _) = _
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem transform_apply (f : FourierSpace N) (α : AddCircle (1 : ℝ)) :
    transform f α = ∑ i : Fin N, (f i : ℂ) * fourier ((i.val : ℤ) + 1) α := by
  simp only [transform, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.sum_apply,
    ContinuousMap.coe_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem coefficient_integral (f : FourierSpace N) (i : Fin N) :
    (∫ α : AddCircle (1 : ℝ),
      conj (fourier ((i.val : ℤ) + 1) α) * transform f α ∂circleHaar) = (f i : ℂ) := by
  simp only [transform_apply, Finset.mul_sum]
  rw [integral_finset_sum]
  · simp_rw [← mul_assoc, mul_comm (conj _), mul_assoc,
      ← smul_eq_mul, integral_smul, smul_eq_mul, integral_conj_fourier_mul]
    have heq (j : Fin N) : ((i.val : ℤ) + 1 = (j.val : ℤ) + 1) ↔ i = j := by
      constructor
      · intro h; apply Fin.ext; omega
      · rintro rfl; rfl
    simp only [heq, mul_ite, mul_one, mul_zero]
    simp
  · intro j _
    exact ((fourier ((i.val : ℤ) + 1)).continuous.star.mul
      (continuous_const.mul (fourier ((j.val : ℤ) + 1)).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem transform_injective : Function.Injective (transform (N := N)) := by
  intro f g h
  funext i
  apply Complex.ofReal_injective
  rw [← coefficient_integral f i, ← coefficient_integral g i, h]

instance : NormedAddCommGroup (FourierSpace N) :=
  NormedAddCommGroup.induced _ _ transform transform_injective

instance : NormedSpace ℝ (FourierSpace N) := NormedSpace.induced ℝ _ _ transform

@[simp] theorem norm_eq (f : FourierSpace N) : ‖f‖ = ‖transform f‖ := rfl

/-- The usual real coordinate pairing, made continuous by finite dimensionality. -/
def pairing (φ : FourierSpace N) : FourierSpace N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => ∑ i : Fin N, f i * φ i
    map_add' := fun f g => by
      change (∑ i : Fin N, (f i + g i) * φ i) = _
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun c f => by
      change (∑ i : Fin N, (c * f i) * φ i) = _
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }

@[simp] theorem pairing_apply (φ f : FourierSpace N) :
    pairing φ f = ∑ i : Fin N, f i * φ i := rfl

def dualNorm (φ : FourierSpace N) : ℝ := ‖pairing φ‖

theorem dualNorm_nonneg (φ : FourierSpace N) : 0 ≤ dualNorm φ := norm_nonneg _

theorem abs_pairing_le (f φ : FourierSpace N) :
    |∑ i : Fin N, f i * φ i| ≤ ‖f‖ * dualNorm φ := by
  simpa only [Real.norm_eq_abs, mul_comm, pairing_apply] using (pairing φ).le_opNorm f

theorem norm_transform_apply_le (f : FourierSpace N) (α : AddCircle (1 : ℝ)) :
    ‖transform f α‖ ≤ ‖f‖ := (transform f).norm_coe_le_norm α

theorem norm_le_sum (f : FourierSpace N) : ‖f‖ ≤ ∑ i : Fin N, |f i| := by
  rw [norm_eq]
  change ‖∑ i : Fin N, (f i) • fourier ((i.val : ℤ) + 1)‖ ≤ _
  calc
    _ ≤ ∑ i : Fin N, ‖(f i) • fourier (T := 1) ((i.val : ℤ) + 1)‖ := norm_sum_le _ _
    _ = ∑ i : Fin N, |f i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact (norm_smul (f i) (fourier (T := 1) ((i.val : ℤ) + 1))).trans
        (by rw [fourier_norm, mul_one, Real.norm_eq_abs])

theorem norm_nonneg_le_sum {f : FourierSpace N} (hf : ∀ i, 0 ≤ f i) :
    ‖f‖ ≤ ∑ i : Fin N, f i := by
  simpa only [abs_of_nonneg (hf _)] using norm_le_sum f


def delta (i : Fin N) : FourierSpace N := fun j => if i = j then 1 else 0

@[simp] theorem transform_delta (i : Fin N) :
    transform (delta i) = fourier (T := 1) ((i.val : ℤ) + 1) := by
  change (∑ j : Fin N, (if i = j then (1 : ℝ) else 0) • fourier (T := 1) ((j.val : ℤ) + 1)) = _
  have ht (j : Fin N) : (if i = j then (1 : ℝ) else 0) • fourier (T := 1) ((j.val : ℤ) + 1) =
      if i = j then fourier (T := 1) ((j.val : ℤ) + 1) else 0 := by
    split_ifs
    · exact one_smul ℝ (fourier (T := 1) ((j.val : ℤ) + 1))
    · exact zero_smul ℝ (fourier (T := 1) ((j.val : ℤ) + 1))
  simp_rw [ht]
  simp

@[simp] theorem norm_delta (i : Fin N) : ‖delta i‖ = 1 := by
  rw [norm_eq, transform_delta, fourier_norm]

@[simp] theorem pairing_delta (φ : FourierSpace N) (i : Fin N) : pairing φ (delta i) = φ i := by
  simp [pairing_apply, delta]

theorem abs_apply_le_dualNorm (φ : FourierSpace N) (i : Fin N) : |φ i| ≤ dualNorm φ := by
  simpa only [pairing_delta, Real.norm_eq_abs, norm_delta, mul_one] using
    (pairing φ).le_opNorm (delta i)

@[simp] theorem transform_zero_apply (f : FourierSpace N) :
    transform f 0 = (∑ i : Fin N, f i : ℝ) := by
  simp only [transform_apply, fourier_eval_zero, mul_one, ← Complex.ofReal_sum]

theorem abs_sum_le_norm (f : FourierSpace N) : |∑ i : Fin N, f i| ≤ ‖f‖ := by
  have h := norm_transform_apply_le f 0
  rw [transform_zero_apply, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

@[simp] theorem pairing_add (φ ψ : FourierSpace N) :
    pairing (φ + ψ) = pairing φ + pairing ψ := by
  ext f
  change (∑ i : Fin N, f i * (φ i + ψ i)) = _
  simp only [mul_add, Finset.sum_add_distrib, ContinuousLinearMap.add_apply, pairing_apply]

@[simp] theorem pairing_smul (a : ℝ) (φ : FourierSpace N) :
    pairing (a • φ) = a • pairing φ := by
  ext f
  change (∑ i : Fin N, f i * (a * φ i)) = a * ∑ i : Fin N, f i * φ i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem pairing_zero : pairing (0 : FourierSpace N) = 0 := by
  ext f
  change (∑ i : Fin N, f i * 0) = 0
  simp

theorem dualNorm_add_le (φ ψ : FourierSpace N) :
    dualNorm (φ + ψ) ≤ dualNorm φ + dualNorm ψ := by
  exact (congrArg norm (pairing_add φ ψ)).trans_le (norm_add_le _ _)

@[simp] theorem dualNorm_smul (a : ℝ) (φ : FourierSpace N) :
    dualNorm (a • φ) = |a| * dualNorm φ := by
  unfold dualNorm
  rw [pairing_smul]
  exact (norm_smul a (pairing φ)).trans (by rw [Real.norm_eq_abs])

@[simp] theorem dualNorm_zero : dualNorm (0 : FourierSpace N) = 0 := by
  simp [dualNorm]

theorem dualNorm_one_le : dualNorm (1 : FourierSpace N) ≤ 1 := by
  apply (pairing (1 : FourierSpace N)).opNorm_le_bound zero_le_one
  intro f
  change |∑ i : Fin N, f i * 1| ≤ 1 * ‖f‖
  simpa only [mul_one, one_mul] using abs_sum_le_norm f

theorem dualNorm_one (hN : 0 < N) : dualNorm (1 : FourierSpace N) = 1 := by
  apply le_antisymm dualNorm_one_le
  have := abs_apply_le_dualNorm (1 : FourierSpace N) ⟨0, hN⟩
  change |(1 : ℝ)| ≤ _ at this
  simpa only [abs_one] using this

theorem fourier_argument_add (n : ℤ) (α β : AddCircle (1 : ℝ)) :
    fourier n (α + β) = fourier n α * fourier n β := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_argument_neg (n : ℤ) (α : AddCircle (1 : ℝ)) :
    fourier n (-α) = conj (fourier n α) := by
  convert (fourier_neg (n := n) (x := α)) using 1
  simp only [fourier_apply, smul_neg, neg_smul]

/-- Real modulation is essential because the dual norm tests real functions. -/
def realModulation (f : FourierSpace N) (z : ℂ) (α : AddCircle (1 : ℝ)) : FourierSpace N :=
  fun i => f i * (z * fourier ((i.val : ℤ) + 1) α).re

theorem transform_realModulation (f : FourierSpace N) (z : ℂ)
    (α β : AddCircle (1 : ℝ)) :
    transform (realModulation f z α) β =
      (z * transform f (β + α) + conj z * transform f (β - α)) / 2 := by
  simp only [transform_apply, realModulation, sub_eq_add_neg, fourier_argument_add,
    fourier_argument_neg, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have h := Complex.add_conj (z * fourier (T := 1) ((i.val : ℤ) + 1) α)
  rw [map_mul] at h
  apply_fun (fun w : ℂ => (f i : ℂ) * w * fourier ((i.val : ℤ) + 1) β / 2) at h
  push_cast at h
  linear_combination -h

theorem norm_realModulation_le (f : FourierSpace N) {z : ℂ} (hz : ‖z‖ = 1)
    (α : AddCircle (1 : ℝ)) : ‖realModulation f z α‖ ≤ ‖f‖ := by
  rw [norm_eq]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro β
  rw [transform_realModulation, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hzc : ‖conj z‖ = 1 := (Complex.abs_conj z).trans hz
  calc
    _ ≤ ‖z * transform f (β + α)‖ + ‖conj z * transform f (β - α)‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by
      simp only [norm_mul, hz, hzc, one_mul]
      exact add_le_add (norm_transform_apply_le _ _) (norm_transform_apply_le _ _)
    _ = _ := by ring

theorem pairing_realModulation (f φ : FourierSpace N) (z : ℂ) (α : AddCircle (1 : ℝ)) :
    pairing φ (realModulation f z α) = (z * transform (f * φ) α).re := by
  simp only [pairing_apply, realModulation, transform_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change f i * (z * fourier ((i.val : ℤ) + 1) α).re * φ i =
    (z * ((↑(f i * φ i) : ℂ) * fourier ((i.val : ℤ) + 1) α)).re
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem norm_mul_le (f φ : FourierSpace N) : ‖f * φ‖ ≤ ‖f‖ * dualNorm φ := by
  rw [norm_eq]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg f) (dualNorm_nonneg φ))).mpr
  intro α
  obtain ⟨z, hz, hzeq⟩ := Complex.exists_norm_eq_mul_self (transform (f * φ) α)
  have h := abs_pairing_le (realModulation f z α) φ
  rw [← pairing_apply, pairing_realModulation, ← hzeq, Complex.ofReal_re,
    abs_of_nonneg (norm_nonneg _)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_realModulation_le f hz α) (dualNorm_nonneg φ))

theorem dualNorm_mul_le (φ ψ : FourierSpace N) :
    dualNorm (φ * ψ) ≤ dualNorm φ * dualNorm ψ := by
  apply (pairing (φ * ψ)).opNorm_le_bound (mul_nonneg (dualNorm_nonneg φ) (dualNorm_nonneg ψ))
  intro f
  have heq : pairing (φ * ψ) f = pairing ψ (f * φ) := by
    simp only [pairing_apply]
    exact Finset.sum_congr rfl fun i _ => by change f i * (φ i * ψ i) = (f i * φ i) * ψ i; ring
  rw [heq, Real.norm_eq_abs]
  calc
    _ ≤ ‖f * φ‖ * dualNorm ψ := abs_pairing_le _ _
    _ ≤ (‖f‖ * dualNorm φ) * dualNorm ψ :=
      mul_le_mul_of_nonneg_right (norm_mul_le f φ) (dualNorm_nonneg ψ)
    _ = _ := by ring


theorem dualNorm_eq_zero_iff (φ : FourierSpace N) : dualNorm φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    funext i
    have hi := abs_apply_le_dualNorm φ i
    rw [h] at hi
    exact abs_nonpos_iff.mp hi
  · rintro rfl
    exact dualNorm_zero

def dualPairingMap : FourierSpace N →L[ℝ] (FourierSpace N →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := pairing
    map_add' := pairing_add
    map_smul' := pairing_smul }

theorem continuous_dualNorm : Continuous (dualNorm (N := N)) := dualPairingMap.continuous.norm

theorem isCompact_fourier_closedBall (R : ℝ) :
    IsCompact {f : FourierSpace N | ‖f‖ ≤ R} := by
  simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : FourierSpace N) R

theorem isCompact_dualNorm_ball {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact {φ : FourierSpace N | dualNorm φ ≤ R} := by
  apply (isCompact_closedBall (0 : FourierSpace N) ((N : ℝ) * R)).of_isClosed_subset
    (isClosed_le continuous_dualNorm continuous_const)
  intro φ hφ
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖φ‖ ≤ ∑ i : Fin N, |φ i| := norm_le_sum φ
    _ ≤ ∑ _ : Fin N, R := Finset.sum_le_sum fun i _ => (abs_apply_le_dualNorm φ i).trans hφ
    _ = _ := by simp

end FourierSpace

end Sidon
