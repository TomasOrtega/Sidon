import Sidon.NumberTheory.LogSmoothedMangoldt
import Sidon.NumberTheory.SmoothingSeries
import Sidon.NumberTheory.SpectralTailBounds
import Sidon.NumberTheory.NegativeSpectralBounds
import Sidon.NumberTheory.RiemannGaussian.RosserSchoenfeldExplicitFormula

/-! Finite-difference smoothing of the literal logarithmic explicit formula. -/

noncomputable section

open MeasureTheory RiemannGaussian
open scoped BigOperators Topology

namespace Sidon

theorem smoothedMangoldt_zero_eq_primePrimitive (t : ℝ) :
    smoothedMangoldt 0 t = RosserSchoenfeldPrimePrimitive.value t := by
  unfold smoothedMangoldt RosserSchoenfeldPrimePrimitive.value
  apply Finset.sum_congr rfl
  intro n _
  rw [smoothedMangoldtTerm, show 0 + 1 = 1 from rfl, heavisidePrimitive_one]
  rfl

def positiveZeroPrimitive (t : ℝ) : ℂ :=
  RosserSchoenfeldZeroPrimitive.value (max t 0)

def positiveTrivialPrimitive (t : ℝ) : ℂ :=
  RosserSchoenfeldTrivialPrimitive.value (max t 0)

theorem continuous_positiveZeroPrimitive : Continuous positiveZeroPrimitive := by
  rw [continuous_iff_continuousAt]
  intro t
  let T := max t 0 + 1
  have hloc : ContinuousOn positiveZeroPrimitive (Set.Iio T) := by
    change ContinuousOn (fun u => ∑' ρ : NontrivialZetaZero,
      RosserSchoenfeldZeroPrimitive.term ρ (max u 0)) (Set.Iio T)
    apply continuousOn_tsum (fun ρ =>
      (show Continuous (fun u => RosserSchoenfeldZeroPrimitive.term ρ (max u 0)) by
        unfold RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
        fun_prop).continuousOn)
      (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (Real.exp T + 1))
    intro ρ u hu
    have huT : max u 0 ≤ T := max_le hu.le (by dsimp [T]; linarith [le_max_right t 0])
    exact (RosserSchoenfeldZeroPrimitive.norm_term_le ρ (le_max_right u 0)).trans
      (mul_le_mul_of_nonneg_right (add_le_add (Real.exp_le_exp.mpr huT) (le_refl (1 : ℝ)))
        (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have htT : t < T := lt_of_le_of_lt (le_max_left t 0) (lt_add_one _)
  exact hloc.continuousAt (Iio_mem_nhds htT)

theorem continuous_positiveTrivialPrimitive : Continuous positiveTrivialPrimitive := by
  exact RosserSchoenfeldTrivialPrimitive.continuousOn_value.comp_continuous
    (continuous_id.max continuous_const) (fun t => le_max_right t 0)

theorem spectralSmoothing_zeroPrimitive (n : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    spectralSmoothing n h RosserSchoenfeldZeroPrimitive.value t =
      ∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℂ) *
        (Complex.exp ((ρ : ℂ) * t) *
          ((Complex.exp ((ρ : ℂ) * h) - 1) / (ρ : ℂ)) ^ (n + 2)) := by
  let T := t + ((n + 2 : ℕ) : ℝ) * h
  have hT : 0 ≤ T := add_nonneg ht (mul_nonneg (Nat.cast_nonneg _) hh)
  have hbound : ∀ (ρ : NontrivialZetaZero) u, u ∈ Set.Icc 0 T →
      ‖RosserSchoenfeldZeroPrimitive.term ρ u‖ ≤ (Real.exp T + 1) *
        ((analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ u hu
    exact (RosserSchoenfeldZeroPrimitive.norm_term_le ρ hu.1).trans
      (mul_le_mul_of_nonneg_right (add_le_add (Real.exp_le_exp.mpr hu.2) (le_refl (1 : ℝ)))
        (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have hs := spectralSmoothing_tsum_of_uniform_bound RosserSchoenfeldZeroPrimitive.term
    (fun ρ => (Real.exp T + 1) *
      ((analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2))
    (fun ρ => by
      unfold RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
      fun_prop)
    (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (Real.exp T + 1))
    (fun ρ => by positivity) hT hbound n hh ht (le_refl T)
  change spectralSmoothing n h (fun u => ∑' ρ, RosserSchoenfeldZeroPrimitive.term ρ u) t = _
  rw [hs]
  apply tsum_congr
  intro ρ
  change spectralSmoothing n h
    (fun u => (analyticZetaZeroMultiplicity ρ : ℂ) * exponentialZeroAtom (ρ : ℂ) u) t = _
  rw [spectralSmoothing_const_mul, spectralSmoothing_exponentialZeroAtom
    (Complex.ne_zero_of_re_pos (NontrivialZetaZero.zero_lt_re ρ))]


theorem spectralSmoothing_mainTerm (n : ℕ) (h t : ℝ) :
    spectralSmoothing n h RosserSchoenfeldExplicitFormula.mainTerm t =
      Complex.exp (t : ℂ) * (Complex.exp (h : ℂ) - 1) ^ (n + 2) := by
  let c := Complex.log 2 + Complex.log Real.pi
  have hf : RosserSchoenfeldExplicitFormula.mainTerm =
      (exponentialZeroAtom 1 + (fun u : ℝ => -c * u + 0)) := by
    funext u
    simp only [RosserSchoenfeldExplicitFormula.mainTerm, Pi.add_apply,
      exponentialZeroAtom, one_mul, one_pow, div_one, add_zero, c]
    ring
  rw [hf, spectralSmoothing_add (continuous_exponentialZeroAtom 1) (by fun_prop),
    spectralSmoothing_affine, add_zero, spectralSmoothing_exponentialZeroAtom one_ne_zero]
  simp

theorem spectralSmoothing_trivialPrimitive_eq_tsum (n : ℕ) {h t : ℝ}
    (hh : 0 ≤ h) (ht : 0 ≤ t) :
    spectralSmoothing n h RosserSchoenfeldTrivialPrimitive.value t =
      ∑' j : ℕ, spectralSmoothing n h (RosserSchoenfeldTrivialPrimitive.term j) t := by
  let T := t + ((n + 2 : ℕ) : ℝ) * h
  exact spectralSmoothing_tsum_of_uniform_bound RosserSchoenfeldTrivialPrimitive.term
    RosserSchoenfeldTrivialPrimitive.weight
    (fun j => by unfold RosserSchoenfeldTrivialPrimitive.term; fun_prop)
    RosserSchoenfeldTrivialPrimitive.hasSum_weight.summable
    (fun j => by unfold RosserSchoenfeldTrivialPrimitive.weight; positivity)
    (add_nonneg ht (mul_nonneg (Nat.cast_nonneg _) hh))
    (fun j u hu => RosserSchoenfeldTrivialPrimitive.norm_term_le j hu.1)
    n hh ht (le_refl T)

theorem trivialTerm_eq_neg_exponentialAtom (j : ℕ) :
    RosserSchoenfeldTrivialPrimitive.term j =
      fun t => (-1 : ℂ) * exponentialZeroAtom (-2 * ((j : ℂ) + 1)) t := by
  funext t
  unfold RosserSchoenfeldTrivialPrimitive.term exponentialZeroAtom
  push_cast
  ring

theorem spectralSmoothing_trivialTerm_norm_le (j n : ℕ) {h t : ℝ}
    (hh : 0 ≤ h) (ht : 0 ≤ t) :
    ‖spectralSmoothing n h (RosserSchoenfeldTrivialPrimitive.term j) t‖ ≤
      (4 * h ^ n) * RosserSchoenfeldTrivialPrimitive.weight j := by
  let z : ℂ := -2 * ((j : ℂ) + 1)
  have hzre : z.re < 0 := by dsimp [z]; simp; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hzre
    norm_num at hzre
  have hnorm : ‖z‖ ^ 2 = 4 * ((j : ℝ) + 1) ^ 2 := by
    have he : z = ((-2 * ((j : ℝ) + 1) : ℝ) : ℂ) := by dsimp [z]; push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [trivialTerm_eq_neg_exponentialAtom, spectralSmoothing_const_mul, norm_mul]
  simp only [norm_neg, norm_one, one_mul]
  have hb := spectralSmoothing_exponentialZeroAtom_norm_le_nonpos hz hzre.le n hh ht
  rw [hnorm] at hb
  convert hb using 1; unfold RosserSchoenfeldTrivialPrimitive.weight; ring

theorem spectralSmoothing_trivialPrimitive_norm_le (n : ℕ) {h t : ℝ}
    (hh : 0 ≤ h) (ht : 0 ≤ t) :
    ‖spectralSmoothing n h RosserSchoenfeldTrivialPrimitive.value t‖ ≤
      (Real.pi ^ 2 / 6) * h ^ n := by
  rw [spectralSmoothing_trivialPrimitive_eq_tsum n hh ht]
  have hs := RosserSchoenfeldTrivialPrimitive.hasSum_weight.summable.mul_left (4 * h ^ n)
  have hnorm := hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => spectralSmoothing_trivialTerm_norm_le j n hh ht)
  calc
    _ ≤ ∑' j : ℕ, ‖spectralSmoothing n h (RosserSchoenfeldTrivialPrimitive.term j) t‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, (4 * h ^ n) * RosserSchoenfeldTrivialPrimitive.weight j :=
      hnorm.tsum_le_tsum (fun j => spectralSmoothing_trivialTerm_norm_le j n hh ht) hs
    _ = _ := by
      rw [tsum_mul_left, RosserSchoenfeldTrivialPrimitive.hasSum_weight.tsum_eq]
      ring


theorem smoothed_explicit_formula (n : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    (((fwdDiff h)^[n + 2] (smoothedMangoldt n) t : ℝ) : ℂ) =
      Complex.exp (t : ℂ) * (Complex.exp (h : ℂ) - 1) ^ (n + 2) -
        (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℂ) *
          (Complex.exp ((ρ : ℂ) * t) *
            ((Complex.exp ((ρ : ℂ) * h) - 1) / (ρ : ℂ)) ^ (n + 2))) +
        spectralSmoothing n h RosserSchoenfeldTrivialPrimitive.value t := by
  let c : ℂ := -1
  let F : ℝ → ℂ :=
    (RosserSchoenfeldExplicitFormula.mainTerm + fun u => c * positiveZeroPrimitive u) +
      positiveTrivialPrimitive
  have hmain : Continuous RosserSchoenfeldExplicitFormula.mainTerm := by
    unfold RosserSchoenfeldExplicitFormula.mainTerm
    fun_prop
  have hz : Continuous (fun u => c * positiveZeroPrimitive u) :=
    continuous_const.mul continuous_positiveZeroPrimitive
  have hident : ∀ u : ℝ, 0 ≤ u → (smoothedMangoldt 0 u : ℂ) = F u := by
    intro u hu
    rw [smoothedMangoldt_zero_eq_primePrimitive,
      RosserSchoenfeldExplicitFormula.prime_eq_spectral hu]
    simp only [RosserSchoenfeldExplicitFormula.spectral, F, c, Pi.add_apply,
      positiveZeroPrimitive, positiveTrivialPrimitive, max_eq_left hu]
    ring
  have hs := spectralSmoothing_congr_nonneg hident n hh ht
  change spectralSmoothing n h (fun u => (smoothedMangoldt 0 u : ℂ)) t =
    spectralSmoothing n h ((RosserSchoenfeldExplicitFormula.mainTerm +
      fun u => c * positiveZeroPrimitive u) + positiveTrivialPrimitive) t at hs
  rw [spectralSmoothing_add (hmain.add hz) continuous_positiveTrivialPrimitive,
    spectralSmoothing_add hmain hz, spectralSmoothing_const_mul,
    spectralSmoothing_mainTerm] at hs
  have hZ : spectralSmoothing n h positiveZeroPrimitive t =
      spectralSmoothing n h RosserSchoenfeldZeroPrimitive.value t :=
    spectralSmoothing_congr_nonneg (fun u hu => by
      simp only [positiveZeroPrimitive, max_eq_left hu]) n hh ht
  have hV : spectralSmoothing n h positiveTrivialPrimitive t =
      spectralSmoothing n h RosserSchoenfeldTrivialPrimitive.value t :=
    spectralSmoothing_congr_nonneg (fun u hu => by
      simp only [positiveTrivialPrimitive, max_eq_left hu]) n hh ht
  rw [hZ, hV, spectralSmoothing_zeroPrimitive n hh ht,
    spectralSmoothing_smoothedMangoldt] at hs
  simpa only [c, neg_one_mul, sub_eq_add_neg] using hs

theorem smoothed_zeta_high_tail_norm_le (n : ℕ) {T h t : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (hwindow : 0 ≤ t + ((n + 2 : ℕ) : ℝ) * h) :
    ‖∑' ρ : NontrivialZetaZero, if T ≤ ‖(ρ : ℂ)‖ then
        (analyticZetaZeroMultiplicity ρ : ℂ) *
          spectralSmoothing n h (exponentialZeroAtom (ρ : ℂ)) t else 0‖ ≤
      (Real.exp (t + ((n + 2 : ℕ) : ℝ) * h) * 2 ^ (n + 2) / T ^ n) *
        ∑' ρ : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 :=
  norm_spectral_tail_le_square_mass (fun ρ : NontrivialZetaZero => (ρ : ℂ))
    (fun ρ => (analyticZetaZeroMultiplicity ρ : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun ρ => (NontrivialZetaZero.zero_lt_re ρ).le)
    (fun ρ => (NontrivialZetaZero.re_lt_one ρ).le)
    RosserSchoenfeldZeroMass.norm_square_mass_summable n hT hh hwindow

end Sidon
