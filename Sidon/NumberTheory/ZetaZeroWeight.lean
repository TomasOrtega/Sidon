module

public import Sidon.NumberTheory.ZeroDensityLayers
public import Sidon.NumberTheory.LogarithmicReserve
public import Sidon.NumberTheory.ZetaZeroFree

@[expose] public section

/-! # Density and a logarithmic strip force weighted zeros to vanish -/

noncomputable section

open Filter Topology

namespace Sidon

theorem eventually_logarithmic_width_floor_reserve {C r q : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hq : 0 < q) (B : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ((B : ℝ) + 2) * Real.log (r * Real.log T) ≤
        q * Nat.floor (r * Real.log T * logarithmicZeroFreeWidth C T) := by
  have hreserve := eventually_logarithmic_width_reserve hC (mul_pos hq hr)
    (2 * ((B : ℝ) + 2) + q)
  have hloglog := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hreserve, Real.tendsto_log_atTop.eventually_gt_atTop 0,
    hloglog.eventually_ge_atTop (max 1 (Real.log r))] with T hres hlog hll
  have hll1 : 1 ≤ Real.log (Real.log T) := (le_max_left _ _).trans hll
  have hllr : Real.log r ≤ Real.log (Real.log T) := (le_max_right _ _).trans hll
  have hlogL : Real.log (r * Real.log T) ≤ 2 * Real.log (Real.log T) := by
    rw [Real.log_mul hr.ne' hlog.ne']
    linarith
  have hfloor := Nat.sub_one_lt_floor
    (r * Real.log T * logarithmicZeroFreeWidth C T)
  have hfloorq := mul_lt_mul_of_pos_left hfloor hq
  have hqll := mul_le_mul_of_nonneg_left hll1 hq.le
  have hB : 0 ≤ (B : ℝ) + 2 := by positivity
  have hlogLB := mul_le_mul_of_nonneg_left hlogL hB
  nlinarith

theorem eventually_zetaZeroWeight_le_inverse_log_sq
    {A K T₀ C U₀ r : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hr : A < r)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ZetaZeroFreeWidth (logarithmicZeroFreeWidth C) U₀) :
    ∀ᶠ T : ℝ in atTop,
      (∑ z ∈ zetaZeroOccurrences T, Real.exp (-r * Real.log T * (1 - z.1.re))) ≤
        (((K / r ^ B) * Real.exp (A / r)) /
          (1 - Real.exp (-(1 - A / r)))) / (r * Real.log T) ^ 2 := by
  have hr0 : 0 < r := hA.trans_lt hr
  have hb : A / r < 1 := (div_lt_one hr0).mpr hr
  have hq : 0 < 1 - A / r := by linarith
  filter_upwards [eventually_logarithmic_width_floor_reserve hC hr0 hq B,
    eventually_ge_atTop T₀, eventually_ge_atTop U₀,
    Real.tendsto_log_atTop.eventually_gt_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hreserve hT₀ hU₀ hlog hT
  have hlog0 : 0 < Real.log T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hL : 0 < r * Real.log T := mul_pos hr0 hlog0
  have hη : 0 ≤ logarithmicZeroFreeWidth C T := by
    unfold logarithmicZeroFreeWidth
    exact div_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hlog0.le _)
      (Real.rpow_nonneg (Real.log_pos hlog).le _))
  have hD : 0 ≤ A * Real.log T := mul_nonneg hA hlog0.le
  have hcount (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
      (((zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re)).card : ℝ) ≤
        (K * (Real.log T) ^ B) * Real.exp ((A * Real.log T) * (1 - σ)) := by
    have hh := hdensity T hT₀ σ hσ0 hσ1
    change (zetaZeroCount σ T : ℝ) ≤ _
    convert hh using 1
    rw [Real.rpow_def_of_pos hTpos]
    ring_nf
  have hcoeff : (K / r ^ B) * (r * Real.log T) ^ B = K * (Real.log T) ^ B := by
    rw [mul_pow]
    field_simp
  have hratio : (A * Real.log T) / (r * Real.log T) = A / r := by
    field_simp
  have hlayers (j : ℕ) :
      ((zeroLayer (zetaZeroOccurrences T) (fun z => z.1.re) (r * Real.log T) j).card : ℝ) ≤
        ((K / r ^ B) * (r * Real.log T) ^ B) * Real.exp ((A / r) * (j + 1)) := by
    rw [hcoeff, ← hratio]
    exact zeroLayer_card_le_of_density (zetaZeroOccurrences T) (fun z => z.1.re)
      hL (mul_nonneg hK (pow_nonneg hlog0.le B)) hD
      (fun z hz => zetaZeroOccurrences_re_bounds hz) hcount j
  have hbound := finite_zero_bound_of_log_reserve (zetaZeroOccurrences T)
    (fun z => z.1.re) hL hη (div_nonneg hK (pow_nonneg hr0.le B)) hb
    (hfree T hU₀) hlayers hreserve
  simpa only [neg_mul] using hbound

theorem tendsto_zetaZeroWeight_of_density_width
    {A K T₀ C U₀ r : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hr : A < r)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ZetaZeroFreeWidth (logarithmicZeroFreeWidth C) U₀) :
    Tendsto (fun T : ℝ =>
      ∑ z ∈ zetaZeroOccurrences T, Real.exp (-r * Real.log T * (1 - z.1.re)))
      atTop (𝓝 0) := by
  have hr0 : 0 < r := hA.trans_lt hr
  have hL := Real.tendsto_log_atTop.const_mul_atTop hr0
  have hsq := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hL
  have hlim := hsq.const_div_atTop
    (((K / r ^ B) * Real.exp (A / r)) / (1 - Real.exp (-(1 - A / r))))
  exact squeeze_zero'
    (Eventually.of_forall fun T => Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)
    (eventually_zetaZeroWeight_le_inverse_log_sq hA hK hC hr hdensity hfree) hlim

theorem tendsto_zetaZeroWeight_rpow_of_density_width
    {A K T₀ C U₀ τ : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hτ : 0 < τ) (hr : A < τ⁻¹)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ZetaZeroFreeWidth (logarithmicZeroFreeWidth C) U₀) :
    Tendsto (fun x : ℝ =>
      ∑ z ∈ zetaZeroOccurrences (x ^ τ), Real.exp (-Real.log x * (1 - z.1.re)))
      atTop (𝓝 0) := by
  have hh := (tendsto_zetaZeroWeight_of_density_width hA hK hC hr hdensity hfree).comp
    (tendsto_rpow_atTop hτ)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply Finset.sum_congr rfl
  intro z _
  rw [Real.log_rpow hx]
  congr 1
  field_simp

theorem tendsto_zetaZeroWeight_seventeen_fiftieths
    {A K T₀ C U₀ : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hr : A < 50 / 17)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ZetaZeroFreeWidth (logarithmicZeroFreeWidth C) U₀) :
    Tendsto (fun x : ℝ =>
      ∑ z ∈ zetaZeroOccurrences (x ^ ((17 : ℝ) / 50)),
        Real.exp (-Real.log x * (1 - z.1.re))) atTop (𝓝 0) := by
  apply tendsto_zetaZeroWeight_rpow_of_density_width hA hK hC (by norm_num)
    (by norm_num; exact hr) hdensity hfree

theorem tendsto_zetaZeroWeight_seventeen_fiftieths_of_density
    {A K T₀ : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hr : A < 50 / 17)
    (hdensity : UniformZetaZeroDensity A B K T₀) :
    Tendsto (fun x : ℝ =>
      ∑ z ∈ zetaZeroOccurrences (x ^ ((17 : ℝ) / 50)),
        Real.exp (-Real.log x * (1 - z.1.re))) atTop (𝓝 0) := by
  obtain ⟨U₀, hfree⟩ := exists_logarithmicZetaZeroFreeWidth
  exact tendsto_zetaZeroWeight_seventeen_fiftieths hA hK (by norm_num) hr hdensity hfree

theorem eventually_zetaZeroWeight_seventeen_fiftieths_le
    {A K T₀ ε : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hr : A < 50 / 17) (hε : 0 < ε)
    (hdensity : UniformZetaZeroDensity A B K T₀) :
    ∀ᶠ x : ℝ in atTop,
      (∑ z ∈ zetaZeroOccurrences (x ^ ((17 : ℝ) / 50)),
        Real.exp (-Real.log x * (1 - z.1.re))) ≤ ε := by
  have hh := tendsto_zetaZeroWeight_seventeen_fiftieths_of_density hA hK hr hdensity
  exact (hh.eventually_lt_const hε).mono fun _ h => h.le

end Sidon
