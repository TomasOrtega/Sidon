module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator

@[expose] public section

/-!
# Finite Fourier sums on the integers

The positive-exponent convention agrees with `fourier` at period one.
-/

noncomputable section

namespace Sidon

/-- The complex indicator of a finite set of integers. -/
def indicatorFinsupp (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.indicator s fun _ _ => 1

@[simp]
theorem indicatorFinsupp_apply (s : Finset ℤ) (n : ℤ) :
    indicatorFinsupp s n = if n ∈ s then 1 else 0 := by
  simp [indicatorFinsupp, Finsupp.indicator_apply]

@[simp]
theorem support_indicatorFinsupp (s : Finset ℤ) :
    (indicatorFinsupp s).support = s := by
  ext n
  simp only [Finsupp.mem_support_iff, indicatorFinsupp_apply]
  split_ifs <;> simp_all

/-- The unnormalized Fourier transform of a finitely supported integer function. -/
def fourierSum (f : ℤ →₀ ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  f.sum fun n c => c • fourier n

theorem fourierSum_apply (f : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    fourierSum f α = f.sum fun n c => c * fourier n α := by
  simp [fourierSum, Finsupp.sum, ContinuousMap.sum_apply, smul_eq_mul]

@[simp]
theorem fourierSum_zero : fourierSum 0 = 0 := by
  simp [fourierSum]

@[simp]
theorem fourierSum_add (f g : ℤ →₀ ℂ) :
    fourierSum (f + g) = fourierSum f + fourierSum g := by
  exact Finsupp.sum_add_index' (fun n => zero_smul ℂ (fourier (T := 1) n))
    fun n a b => add_smul a b (fourier (T := 1) n)

@[simp]
theorem fourierSum_sub (f g : ℤ →₀ ℂ) :
    fourierSum (f - g) = fourierSum f - fourierSum g := by
  exact Finsupp.sum_sub_index fun n a b => sub_smul a b (fourier (T := 1) n)

@[simp]
theorem fourierSum_smul (c : ℂ) (f : ℤ →₀ ℂ) :
    fourierSum (c • f) = c • fourierSum f := by
  rw [fourierSum, Finsupp.sum_smul_index
    (h := fun n z => z • fourier (T := 1) n) (fun n => zero_smul ℂ (fourier n))]
  simp only [fourierSum, mul_smul, Finsupp.sum, Finset.smul_sum]

@[simp]
theorem fourierSum_real_smul (c : ℝ) (f : ℤ →₀ ℂ) :
    fourierSum (c • f) = c • fourierSum f := by
  have heq : c • f = (c : ℂ) • f := by ext x; simp [Complex.real_smul]
  rw [heq, fourierSum_smul]
  rfl

theorem fourierSum_indicatorFinsupp_apply (s : Finset ℤ) (α : AddCircle (1 : ℝ)) :
    fourierSum (indicatorFinsupp s) α = ∑ n ∈ s, fourier n α := by
  rw [fourierSum_apply, Finsupp.sum, support_indicatorFinsupp]
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

theorem fourierSum_indicatorFinsupp (s : Finset ℤ) :
    fourierSum (indicatorFinsupp s) = ∑ n ∈ s, fourier n := by
  ext α
  simp only [fourierSum_indicatorFinsupp_apply, ContinuousMap.sum_apply]

theorem norm_fourierSum_le (f : ℤ →₀ ℂ) :
    ‖fourierSum f‖ ≤ f.sum fun _ c => ‖c‖ := by
  calc
    ‖fourierSum f‖ ≤ ∑ n ∈ f.support, ‖f n • fourier (T := 1) n‖ :=
      norm_sum_le _ _
    _ = f.sum fun _ c => ‖c‖ := by
      apply Finset.sum_congr rfl
      intro n _
      exact (norm_smul (f n) (fourier (T := 1) n)).trans (by rw [fourier_norm, mul_one])

theorem norm_fourierSum_apply_le (f : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    ‖fourierSum f α‖ ≤ f.sum fun _ c => ‖c‖ :=
  ((fourierSum f).norm_coe_le_norm α).trans (norm_fourierSum_le f)

theorem fourierSum_apply_zero (f : ℤ →₀ ℂ) :
    fourierSum f 0 = f.sum fun _ c => c := by
  simp only [fourierSum_apply, fourier_eval_zero, mul_one]

@[simp]
theorem fourierSum_indicatorFinsupp_zero (s : Finset ℤ) :
    fourierSum (indicatorFinsupp s) 0 = (s.card : ℂ) := by
  simp only [fourierSum_indicatorFinsupp_apply, fourier_eval_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]

@[simp]
theorem norm_fourierSum_indicatorFinsupp_zero (s : Finset ℤ) :
    ‖fourierSum (indicatorFinsupp s) 0‖ = (s.card : ℝ) := by
  simp

@[simp]
theorem norm_fourierSum_indicatorFinsupp (s : Finset ℤ) :
    ‖fourierSum (indicatorFinsupp s)‖ = (s.card : ℝ) := by
  apply le_antisymm
  · calc
      ‖fourierSum (indicatorFinsupp s)‖ ≤ (indicatorFinsupp s).sum fun _ c => ‖c‖ :=
        norm_fourierSum_le _
      _ = (s.card : ℝ) := by
        rw [Finsupp.sum, support_indicatorFinsupp]
        calc
          ∑ n ∈ s, ‖indicatorFinsupp s n‖ = ∑ _ ∈ s, (1 : ℝ) :=
            Finset.sum_congr rfl fun n hn => by rw [indicatorFinsupp_apply, if_pos hn, norm_one]
          _ = (s.card : ℝ) := by simp
  · simpa using (fourierSum (indicatorFinsupp s)).norm_coe_le_norm 0

end Sidon
