import Sidon.Analysis.FiniteFourier
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! # Finite correlations and integer translations -/

noncomputable section

open scoped ComplexConjugate

namespace Sidon

/-- Translation with the convention `integerShift h f x = f (x + h)`. -/
def integerShift (h : ℤ) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  f.mapDomain fun x => x - h

@[simp]
theorem integerShift_apply (h : ℤ) (f : ℤ →₀ ℂ) (x : ℤ) :
    integerShift h f x = f (x + h) := by
  simpa only [integerShift, add_sub_cancel_right] using
    Finsupp.mapDomain_apply (f := fun y : ℤ => y - h)
      (fun a b hab => by change a - h = b - h at hab; omega) f (x + h)

theorem sum_integerShift (h : ℤ) (f : ℤ →₀ ℂ) :
    (integerShift h f).sum (fun _ c => c) = f.sum (fun _ c => c) := by
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

@[simp]
theorem integerShift_zero (f : ℤ →₀ ℂ) : integerShift 0 f = f := by
  ext x
  simp

/-- The correlation at displacement `h`, with conjugation in the second argument. -/
def correlation (f g : ℤ →₀ ℂ) (h : ℤ) : ℂ :=
  f.sum fun x c => c * conj (g (x + h))

theorem correlation_eq_sum (s : Finset ℤ) (f g : ℤ →₀ ℂ) (h : ℤ)
    (hf : f.support ⊆ s) :
    correlation f g h = ∑ x ∈ s, f x * conj (g (x + h)) := by
  apply Finset.sum_subset hf
  intro x _ hx
  change f x * conj (g (x + h)) = 0
  rw [Finsupp.not_mem_support_iff.mp hx, zero_mul]

@[simp]
theorem correlation_zero_left (g : ℤ →₀ ℂ) (h : ℤ) : correlation 0 g h = 0 := by
  simp [correlation]

@[simp]
theorem correlation_zero_right (f : ℤ →₀ ℂ) (h : ℤ) : correlation f 0 h = 0 := by
  simp [correlation, Finsupp.sum]

theorem correlation_add_left (f₁ f₂ g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (f₁ + f₂) g h = correlation f₁ g h + correlation f₂ g h := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

theorem correlation_add_right (f g₁ g₂ : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (g₁ + g₂) h = correlation f g₁ h + correlation f g₂ h := by
  simp [correlation, Finsupp.sum, mul_add, Finset.sum_add_distrib]

theorem correlation_sub_left (f₁ f₂ g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (f₁ - f₂) g h = correlation f₁ g h - correlation f₂ g h := by
  exact Finsupp.sum_sub_index fun _ a b => sub_mul a b _

theorem correlation_sub_right (f g₁ g₂ : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (g₁ - g₂) h = correlation f g₁ h - correlation f g₂ h := by
  simp [correlation, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

theorem correlation_smul_left (c : ℂ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (c • f) g h = c * correlation f g h := by
  rw [correlation, Finsupp.sum_smul_index
    (h := fun x a => a * conj (g (x + h))) (fun _ => zero_mul _)]
  simp only [correlation, Finsupp.sum, mul_assoc, Finset.mul_sum]

theorem correlation_smul_right (c : ℂ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (c • g) h = conj c * correlation f g h := by
  simp only [correlation, Finsupp.smul_apply, smul_eq_mul, map_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem correlation_real_smul_left (c : ℝ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (c • f) g h = c • correlation f g h := by
  have heq : c • f = (c : ℂ) • f := by ext x; simp [Complex.real_smul]
  rw [heq, correlation_smul_left, Complex.real_smul]

theorem correlation_real_smul_right (c : ℝ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (c • g) h = c • correlation f g h := by
  have heq : c • g = (c : ℂ) • g := by ext x; simp [Complex.real_smul]
  rw [heq, correlation_smul_right, Complex.conj_ofReal, Complex.real_smul]

theorem correlation_sum_left {ι : Type*} (s : Finset ι) (F : ι → ℤ →₀ ℂ)
    (g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (∑ i ∈ s, F i) g h = ∑ i ∈ s, correlation (F i) g h := by
  exact Finsupp.sum_sum_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

theorem correlation_sum_right {ι : Type*} (s : Finset ι) (F : ι → ℤ →₀ ℂ)
    (f : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (∑ i ∈ s, F i) h = ∑ i ∈ s, correlation f (F i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, correlation_add_right, ih, Finset.sum_insert hi]

theorem correlation_integerShift (u v : ℤ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (integerShift u f) (integerShift v g) h = correlation f g (h + v - u) := by
  unfold correlation integerShift
  rw [Finsupp.sum_mapDomain_index
    (h := fun x c => c * conj ((g.mapDomain fun y => y - v) (x + h)))
    (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  change (f.sum fun x c => c * conj (integerShift v g (x - u + h))) = _
  simp only [integerShift_apply]
  congr 1
  funext x c
  rw [show x - u + h + v = x + (h + v - u) by omega]

theorem correlation_swap_zero (f g : ℤ →₀ ℂ) :
    correlation g f 0 = conj (correlation f g 0) := by
  rw [correlation_eq_sum (f.support ∪ g.support) g f 0 (Finset.subset_union_right ..),
    correlation_eq_sum (f.support ∪ g.support) f g 0 (Finset.subset_union_left ..)]
  simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, starRingEnd_self_apply,
    RingHom.id_apply, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem correlation_swap_neg (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation g f h = conj (correlation f g (-h)) := by
  calc
    correlation g f h = correlation g (integerShift h f) 0 := by
      simpa using (correlation_integerShift 0 h g f 0).symm
    _ = conj (correlation (integerShift h f) g 0) := correlation_swap_zero _ _
    _ = conj (correlation f g (-h)) := by
      congr 1
      simpa using correlation_integerShift h 0 f g 0

theorem correlation_self_zero (f : ℤ →₀ ℂ) :
    correlation f f 0 = f.sum fun _ c => (Complex.normSq c : ℂ) := by
  simp only [correlation, Finsupp.sum, add_zero, Complex.mul_conj]

theorem re_correlation_self_zero (f : ℤ →₀ ℂ) :
    (correlation f f 0).re = f.sum fun _ c => Complex.normSq c := by
  rw [correlation_self_zero]
  simp [Finsupp.sum]

theorem re_correlation_self_zero_nonneg (f : ℤ →₀ ℂ) :
    0 ≤ (correlation f f 0).re := by
  rw [re_correlation_self_zero]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem correlation_eq_zero_of_not_mem (f g : ℤ →₀ ℂ) (h : ℤ)
    (hh : h ∉ (f.support ×ˢ g.support).image (fun p => p.2 - p.1)) :
    correlation f g h = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hg : g (x + h) = 0 := by
    by_contra hg
    apply hh
    exact Finset.mem_image.mpr ⟨(x, x + h),
      Finset.mem_product.mpr ⟨hx, Finsupp.mem_support_iff.mpr hg⟩, by simp⟩
  simp [hg]

theorem correlation_finiteSupport (f g : ℤ →₀ ℂ) :
    (Function.support (correlation f g)).Finite := by
  apply ((f.support ×ˢ g.support).image (fun p => p.2 - p.1)).finite_toSet.subset
  intro h hh
  by_contra hnot
  exact hh (correlation_eq_zero_of_not_mem f g h hnot)

theorem norm_fourier_apply (n : ℤ) (α : AddCircle (1 : ℝ)) :
    ‖fourier n α‖ = 1 := Circle.abs_coe _

/-- Multiplication by a character preserves finite support. -/
def fourierTwist (α : AddCircle (1 : ℝ)) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset f.support (fun x => f x * fourier x α) fun x hx =>
    Finsupp.mem_support_iff.mpr fun hf => hx (by
      change f x * fourier x α = 0
      rw [hf, zero_mul])

@[simp]
theorem fourierTwist_apply (α : AddCircle (1 : ℝ)) (f : ℤ →₀ ℂ) (x : ℤ) :
    fourierTwist α f x = f x * fourier x α := rfl

@[simp]
theorem support_fourierTwist (α : AddCircle (1 : ℝ)) (f : ℤ →₀ ℂ) :
    (fourierTwist α f).support = f.support := by
  ext x
  have hχ : fourier x α ≠ 0 := by
    intro hx
    have := norm_fourier_apply x α
    rw [hx, norm_zero] at this
    exact zero_ne_one this
  simp [Finsupp.mem_support_iff, hχ]

theorem sum_fourierTwist (α : AddCircle (1 : ℝ)) (f : ℤ →₀ ℂ) :
    (fourierTwist α f).sum (fun _ c => c) = fourierSum f α := by
  rw [fourierSum_apply, Finsupp.sum, support_fourierTwist]
  rfl

theorem correlation_fourierTwist (α : AddCircle (1 : ℝ)) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation (fourierTwist α f) (fourierTwist α g) h =
      fourier (-h) α * correlation f g h := by
  simp only [correlation, Finsupp.sum, support_fourierTwist, fourierTwist_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hχ : fourier x α * conj (fourier x α) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_fourier_apply, one_pow,
      Complex.ofReal_one]
  simp only [fourier_add, map_mul, fourier_neg]
  calc
    f x * fourier x α * (conj (g (x + h)) * (conj (fourier x α) * conj (fourier h α))) =
        (fourier x α * conj (fourier x α)) *
          (conj (fourier h α) * (f x * conj (g (x + h)))) := by ring
    _ = _ := by rw [hχ, one_mul]

theorem norm_correlation_fourierTwist (α : AddCircle (1 : ℝ)) (f g : ℤ →₀ ℂ) (h : ℤ) :
    ‖correlation (fourierTwist α f) (fourierTwist α g) h‖ = ‖correlation f g h‖ := by
  rw [correlation_fourierTwist, norm_mul, norm_fourier_apply, one_mul]

end Sidon
