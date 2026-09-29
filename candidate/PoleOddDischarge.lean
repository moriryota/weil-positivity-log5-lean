import PoleParity
import ColL2Components
import TailSupport
import FTCIntegral
import BandNorm

open MeasureTheory Set intervalIntegral
open RHConditionalLog5 RHResidualMembership RHWeilColumnCandidate RHLog5Bridge
open RHConcreteParameters RHRealWeil RHWeilShift RH_LiteratureBridge RHPoleParity RHColL2 RHBandNorm

lemma zeroSinh_memLp (L : ℝ) : MemLp (zeroSinh L) 2 volume := by
  have hs : MemLp (fun x => Real.sinh (x / 2)) 2 (volume.restrict (Icc (-L) L)) :=
    sinh_half_memLp L
  exact (memLp_indicator_iff_restrict measurableSet_Icc).mpr hs

lemma tail_mul_sinh_eq_zeroSinh (u : ℝ → ℝ) (hu : Test u) (x : ℝ) :
    tail true u x * Real.sinh (x / 2) = tail true u x * zeroSinh halfWidth x := by
  unfold zeroSinh indicator
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · rw [if_pos hx]
  · rw [if_neg hx, mul_zero]
    have h_abs : |x| > halfWidth := by
      change ¬ (-halfWidth ≤ x ∧ x ≤ halfWidth) at hx
      rw [not_and] at hx
      by_cases h1 : -halfWidth ≤ x
      · have h2 : halfWidth < x := lt_of_not_ge (hx h1)
        have : 0 < x := by linarith [RHLog5Bridge.halfWidth_pos]
        rw [abs_of_pos this]
        linarith
      · have h2 : x < -halfWidth := lt_of_not_ge h1
        have : x < 0 := by linarith [RHLog5Bridge.halfWidth_pos]
        rw [abs_of_neg this]
        linarith
    rw [tail_eq_zero_of_not_mem true u hu x h_abs, zero_mul]

namespace RHPoleParity

/-- Transfer from Lp norm-squared to Lebesgue integral of square. -/
lemma embed_norm_sq (v : ℝ → ℝ) (hv : MemLp v 2 volume) :
    ‖embed v‖^2 = ∫ x, (v x)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_embed v v hv hv]
  simp [sq]

/-- Cauchy-Schwarz inequality for embed of two L^2 functions on ℝ. -/
lemma cs_embed_sq (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, f x * g x)^2 ≤ (∫ x, (f x)^2) * (∫ x, (g x)^2) := by
  have hcs := abs_real_inner_le_norm (embed f) (embed g)
  have habs : 0 ≤ |inner ℝ (embed f) (embed g)| := abs_nonneg _
  have hnn : 0 ≤ ‖embed f‖ * ‖embed g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (inner ℝ (embed f) (embed g))^2 ≤ (‖embed f‖ * ‖embed g‖)^2 := by
    rw [← sq_abs (inner ℝ (embed f) (embed g))]
    nlinarith [habs, hcs, hnn]
  rw [mul_pow] at hsq
  rw [inner_embed f g hf hg] at hsq
  rw [embed_norm_sq f hf, embed_norm_sq g hg] at hsq
  exact hsq

/-- Unconditional lower bound on the odd sector sinh moment via Cauchy-Schwarz and FTC. -/
theorem tail_true_sinh_integral_sq_le (u : ℝ → ℝ) (hu : Test u) :
    (∫ x, tail true u x * Real.sinh (x / 2))^2 ≤
      (∫ x, (tail true u x)^2) * (Real.sinh halfWidth - halfWidth) := by
  have h_tail_mem : MemLp (tail true u) 2 volume := tail_memLp true u hu
  have h_sinh_mem : MemLp (zeroSinh halfWidth) 2 volume := zeroSinh_memLp halfWidth
  have heq_int : (∫ x, tail true u x * Real.sinh (x / 2)) =
      ∫ x, tail true u x * zeroSinh halfWidth x := by
    congr 1
    ext x
    exact tail_mul_sinh_eq_zeroSinh u hu x
  rw [heq_int]
  have hcs := cs_embed_sq (tail true u) (zeroSinh halfWidth) h_tail_mem h_sinh_mem
  have h_int_sinh := zeroSinh_sq_integral halfWidth (le_of_lt halfWidth_pos)
  rw [h_int_sinh] at hcs
  exact hcs

/-- Unconditional odd sector pole lower bound discharging hpole completely. -/
theorem hpole_odd_unconditional (u : ℝ → ℝ) (hu : Test u) :
    - P_penalty * (∫ x, (tail true u x)^2) ≤
      2 * (∫ x, tail true u x * Real.cosh (x / 2))^2 -
      2 * (∫ x, tail true u x * Real.sinh (x / 2))^2 := by
  rw [odd_pole_eq_neg_sinh_sq u]
  have hcs := tail_true_sinh_integral_sq_le u hu
  have _h_sq : 0 ≤ ∫ x, (tail true u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  unfold P_penalty
  have hL : RHWeilShift.L = halfWidth := rfl
  rw [hL]
  nlinarith

/-- Discharged version of odd_shift_of_analytic eliminating the hpole hypothesis completely. -/
theorem odd_shift_of_analytic_discharged
    (h_shift_le : concrete.shift true ≤ c_odd)
    (u : ℝ → ℝ) (hu : Test u)
    (hE : compare (tail true u) + T_tail * (∫ x, (tail true u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail true u x - tail true u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail true u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail true u x)^2)) :
    compare (tail true u) + concrete.shift true * (∫ x, (tail true u x)^2) ≤ spatial_weil (tail true u) :=
  odd_shift_of_analytic h_shift_le u hu hE hprime (hpole_odd_unconditional u hu)


end RHPoleParity
