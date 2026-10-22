import Sidon.Analysis.TorusFourier
import Sidon.Analysis.Correlation

/-! # Testing integer Fourier discrepancy against torus character series -/

noncomputable section

namespace Sidon

variable {d : ℕ}

def torusFrequency (n : Fin d → ℤ) (α : Fin d → AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  ∑ i, n i • α i

theorem fourier_add_argument (n : ℤ) (α β : AddCircle (1 : ℝ)) :
    fourier n (α + β) = fourier n α * fourier n β := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_interchange_index (m n : ℤ) (α : AddCircle (1 : ℝ)) :
    fourier m (n • α) = fourier n (m • α) := by
  simp only [fourier_apply, smul_comm m n]

theorem fourier_sum_argument {ι : Type*} (s : Finset ι) (n : ℤ)
    (α : ι → AddCircle (1 : ℝ)) :
    fourier n (∑ i ∈ s, α i) = ∏ i ∈ s, fourier n (α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using fourier_eval_zero (T := 1) n
  | @insert i s hi h =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add_argument, h]

theorem torusCharacter_zsmul (n : Fin d → ℤ) (α : Fin d → AddCircle (1 : ℝ)) (x : ℤ) :
    torusCharacter n (x • α) = fourier x (torusFrequency n α) := by
  rw [torusCharacter_apply, torusFrequency, fourier_sum_argument]
  apply Finset.prod_congr rfl
  intro i _
  exact fourier_interchange_index (n i) x (α i)

/-- Testing an integer coefficient function along an orbit in the torus. -/
def torusTest (f : ℤ →₀ ℂ) (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (α : Fin d → AddCircle (1 : ℝ)) : ℂ :=
  f.sum fun x c => c * F (x • α)

theorem torusTest_character (f : ℤ →₀ ℂ) (n : Fin d → ℤ)
    (α : Fin d → AddCircle (1 : ℝ)) :
    torusTest f (torusCharacter n) α = fourierSum f (torusFrequency n α) := by
  simp only [torusTest, torusCharacter_zsmul, fourierSum_apply]

theorem hasSum_torusTest_series (f : ℤ →₀ ℂ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (a : (Fin d → ℤ) → ℂ)
    (hF : ∀ β, HasSum (fun n => a n * torusCharacter n β) (F β))
    (α : Fin d → AddCircle (1 : ℝ)) :
    HasSum (fun n => a n * fourierSum f (torusFrequency n α)) (torusTest f F α) := by
  have h := hasSum_sum (s := f.support) (fun x _ => (hF (x • α)).mul_left (f x))
  change HasSum _ (torusTest f F α) at h
  convert h using 1
  ext n
  rw [fourierSum_apply, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← torusCharacter_zsmul]
  ring

theorem norm_torusTest_le_fourier_bound (f : ℤ →₀ ℂ)
    (F : (Fin d → AddCircle (1 : ℝ)) → ℂ) (a : (Fin d → ℤ) → ℂ)
    (ha : Summable (fun n => ‖a n‖))
    (hF : ∀ β, HasSum (fun n => a n * torusCharacter n β) (F β))
    (α : Fin d → AddCircle (1 : ℝ)) (D : ℝ)
    (hD : ∀ β, ‖fourierSum f β‖ ≤ D) :
    ‖torusTest f F α‖ ≤ D * ∑' n, ‖a n‖ := by
  have hs := hasSum_torusTest_series f F a hF α
  have hb := ha.hasSum.mul_left D
  apply hs.norm_le_of_bounded hb
  intro n
  rw [norm_mul]
  calc
    ‖a n‖ * ‖fourierSum f (torusFrequency n α)‖ ≤ ‖a n‖ * D :=
      mul_le_mul_of_nonneg_left (hD _) (norm_nonneg _)
    _ = D * ‖a n‖ := mul_comm _ _

theorem norm_torusTest_sub_le (f : ℤ →₀ ℂ)
    (F G : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (α : Fin d → AddCircle (1 : ℝ)) (ε : ℝ)
    (hε : ∀ β, ‖F β - G β‖ ≤ ε) :
    ‖torusTest f F α - torusTest f G α‖ ≤
      ε * f.sum (fun _ c => ‖c‖) := by
  rw [torusTest, torusTest, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ x ∈ f.support, (f x * F (x • α) - f x * G (x • α))‖ ≤
        ∑ x ∈ f.support, ‖f x * F (x • α) - f x * G (x • α)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ f.support, ‖f x‖ * ε := by
      apply Finset.sum_le_sum
      intro x _
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hε _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

end Sidon
