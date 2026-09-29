import ColL2Components
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Set intervalIntegral

noncomputable def zeroSinh (L : ℝ) (x : ℝ) : ℝ :=
  (Icc (-L) L).indicator (fun y => Real.sinh (y / 2)) x

lemma sinh_sub_id_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sinh t - t) (2 * Real.sinh (x / 2)^2) x := by
  have h1 : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have h2 : HasDerivAt id 1 x := hasDerivAt_id x
  have hsub := h1.sub h2
  have heq : Real.cosh x - 1 = 2 * Real.sinh (x / 2)^2 := by
    have hcos : Real.cosh (2 * (x / 2)) = 2 * Real.sinh (x / 2)^2 + 1 := by
      rw [Real.cosh_two_mul]
      rw [Real.cosh_sq]
      ring
    have h2 : 2 * (x / 2) = x := mul_div_cancel₀ x two_ne_zero
    rw [h2] at hcos
    linarith
  rw [heq] at hsub
  exact hsub

lemma continuous_sinh_sq : Continuous (fun x : ℝ => 2 * Real.sinh (x / 2)^2) := by
  continuity

lemma integral_two_sinh_sq (L : ℝ) :
    ∫ x in -L..L, 2 * Real.sinh (x / 2)^2 = 2 * (Real.sinh L - L) := by
  have h_deriv : ∀ x ∈ uIcc (-L) L, HasDerivAt (fun t => Real.sinh t - t) (2 * Real.sinh (x / 2)^2) x :=
    fun x _ => sinh_sub_id_hasDerivAt x
  have h_int : IntervalIntegrable (fun x => 2 * Real.sinh (x / 2)^2) volume (-L) L :=
    continuous_sinh_sq.intervalIntegrable (-L) L
  have h := integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h]
  simp only [Real.sinh_neg]
  ring

lemma integral_sinh_sq (L : ℝ) :
    ∫ x in -L..L, Real.sinh (x / 2)^2 = Real.sinh L - L := by
  have h := integral_two_sinh_sq L
  rw [intervalIntegral.integral_const_mul] at h
  linarith

lemma zeroSinh_sq_integral (L : ℝ) (hL : 0 ≤ L) :
    ∫ x, (zeroSinh L x)^2 = Real.sinh L - L := by
  have h_le : -L ≤ L := by linarith
  have heq_ind : (fun x => (zeroSinh L x)^2) = (Icc (-L) L).indicator (fun y => Real.sinh (y / 2)^2) := by
    ext x
    unfold zeroSinh indicator
    by_cases hx : x ∈ Icc (-L) L
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, zero_pow two_ne_zero]
  rw [heq_ind]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le h_le]
  exact integral_sinh_sq L
