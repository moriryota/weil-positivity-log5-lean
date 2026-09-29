/-
Released under Apache 2.0 license.
-/

import Zeta23.ExplicitFormula
import Zeta23.WeilEF.Main
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Zeta23.GammaFacts.Series
import Zeta23.Poisson.PaperFT
import Zeta23.Taper.Fourier

/-! ==========================================================================
  PART A: Gamma Tail Closed-Form (From Task 0032 / GammaTail.lean)
  ========================================================================== -/

/-
Released under Apache 2.0 license.
-/


/-!
# Gamma Tail Integral Formalization

This module establishes the exact equivalence between the Archimedean Gamma tail integral
of the kernel $K(x) = \frac{e^{x/2}}{\sinh x}$ and its analytical closed-form expression
$T(b) = 2(\operatorname{artanh}(e^{-b/2}) + \arctan(e^{-b/2}))$ for $b > 0$.

## Main Results
- `RH_Rebaseline.K_kernel_eq`: Equivalence of hyperbolic and exponential fraction forms of $K(x)$.
- `RH_Rebaseline.T_tail_pos`: Positivity of $T(b)$ for $b > 0$.
- `RH_Rebaseline.hasDerivAt_artanh`: Derivative of $\operatorname{artanh}$ on $(-1, 1)$.
- `RH_Rebaseline.hasDerivAt_T_tail`: Derivative $T'(x) = - K(x)$ for $x > 0$.
- `RH_Rebaseline.tendsto_T_tail_atTop`: Asymptotic vanishing $\lim_{x \to \infty} T(x) = 0$.
- `RH_Rebaseline.integrableOn_Ioi_K_kernel`: Integrability of $K(x)$ on $(b, \infty)$ for $b > 0$.
- `RH_Rebaseline.integral_Ioi_K_kernel_eq_T_tail`: Exact equality $\int_{(b, \infty)} K(x) dx = T(b)$.
- `RH_Rebaseline.integral_Ici_K_kernel_eq_T_tail`: Exact equality $\int_{[b, \infty)} K(x) dx = T(b)$.
-/

open Set Filter
open scoped Topology MeasureTheory

namespace RH_Rebaseline

/-! ## Part 1: Definitions and Basic Properties of Kernel and Closed-Form Tail -/

/-- Archimedean kernel in hyperbolic form:
  `K_kernel x = exp(x / 2) / sinh x`. -/
noncomputable def K_kernel (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sinh x

/-- Archimedean kernel in exponential fraction form:
  `K_kernel_alt x = 2 exp(-x / 2) / (1 - exp(-2x))`. -/
noncomputable def K_kernel_alt (x : ℝ) : ℝ :=
  2 * Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

/-- Equivalence of the two representations of the Archimedean kernel for $x > 0$. -/
theorem K_kernel_eq (x : ℝ) (_hx : 0 < x) :
    K_kernel x = K_kernel_alt x := by
  unfold K_kernel K_kernel_alt
  rw [Real.sinh_eq]
  have h_exp_neg_mul : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    have h_zero : x + -x = 0 := by ring
    rw [h_zero]
    exact Real.exp_zero
  have h_num : 2 * Real.exp (x / 2) * Real.exp (-x) = 2 * Real.exp (-x / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have h_denom : (Real.exp x - Real.exp (-x)) * Real.exp (-x) = 1 - Real.exp (-2 * x) := by
    rw [sub_mul, h_exp_neg_mul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have h_div_two : Real.exp (x / 2) / ((Real.exp x - Real.exp (-x)) / 2) =
      2 * Real.exp (x / 2) / (Real.exp x - Real.exp (-x)) := by
    rw [div_div_eq_mul_div]
    ring
  rw [h_div_two]
  rw [← h_num, ← h_denom]
  exact (mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos (-x)))).symm

/-- Analytical closed-form expression of the tail function:
  `T_tail b = 2 * (artanh(exp(-b / 2)) + arctan(exp(-b / 2)))`.
  (Note: Prior to integration proof below, this is defined purely as an algebraic expression). -/
noncomputable def T_tail (b : ℝ) : ℝ :=
  2 * (Real.artanh (Real.exp (-b / 2)) + Real.arctan (Real.exp (-b / 2)))

/-- Positivity of the closed-form tail for $b > 0$. -/
theorem T_tail_pos {b : ℝ} (hb : 0 < b) : 0 < T_tail b := by
  unfold T_tail
  have h_exp_pos : 0 < Real.exp (-b / 2) := Real.exp_pos (-b / 2)
  have h_exp_lt_one : Real.exp (-b / 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_mem : Real.exp (-b / 2) ∈ Set.Ioo 0 1 := ⟨h_exp_pos, h_exp_lt_one⟩
  have h_artanh_pos : 0 < Real.artanh (Real.exp (-b / 2)) :=
    Real.artanh_pos h_mem
  have h_atan_pos : 0 < Real.arctan (Real.exp (-b / 2)) :=
    Real.arctan_pos.mpr h_exp_pos
  linarith

/-! ## Part 2: Derivatives and Asymptotics -/

/-- Derivative of `Real.artanh` at any point $u \in (-1, 1)$ is $\frac{1}{1 - u^2}$. -/
theorem hasDerivAt_artanh {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - u ^ 2)) u := by
  have hu_pos : 0 < 1 + u := by linarith [hu.1]
  have hu_pos' : 0 < 1 - u := by linarith [hu.2]
  have hlog1 : HasDerivAt Real.log (1 + u)⁻¹ (1 + u) :=
    Real.hasDerivAt_log (ne_of_gt hu_pos)
  have h_comp1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 + u)⁻¹ u :=
    hlog1.comp_const_add 1 u
  have hlog2 : HasDerivAt Real.log (1 - u)⁻¹ (1 - u) :=
    Real.hasDerivAt_log (ne_of_gt hu_pos')
  have h_comp2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - u)⁻¹) u :=
    hlog2.comp_const_sub 1 u
  have h_sub : HasDerivAt (fun x : ℝ => Real.log (1 + x) - Real.log (1 - x))
      ((1 + u)⁻¹ - (-(1 - u)⁻¹)) u := h_comp1.sub h_comp2
  have h_half : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x)))
      ((1 / 2 : ℝ) * ((1 + u)⁻¹ - (-(1 - u)⁻¹))) u := HasDerivAt.const_mul (1 / 2 : ℝ) h_sub
  have h_deriv_eq : (1 / 2 : ℝ) * ((1 + u)⁻¹ - (-(1 - u)⁻¹)) = 1 / (1 - u ^ 2) := by
    have hne1 : 1 + u ≠ 0 := ne_of_gt hu_pos
    have hne2 : 1 - u ≠ 0 := ne_of_gt hu_pos'
    have h_denom : 1 - u ^ 2 = (1 + u) * (1 - u) := by ring
    rw [h_denom]
    simp only [sub_neg_eq_add, inv_eq_one_div]
    field_simp
    ring
  rw [h_deriv_eq] at h_half
  refine h_half.congr_of_eventuallyEq ?_
  have h_nhds : Ioo (-1 : ℝ) 1 ∈ 𝓝 u := Ioo_mem_nhds hu.1 hu.2
  filter_upwards [h_nhds] with x hx
  have hx_pos : 0 < 1 + x := by linarith [hx.1]
  have hx_pos' : 0 < 1 - x := by linarith [hx.2]
  have hx_icc : x ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  rw [Real.artanh_eq_half_log hx_icc]
  have h_log_div : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
    Real.log_div (ne_of_gt hx_pos) (ne_of_gt hx_pos')
  rw [h_log_div]

/-- Derivative of the base decay factor $x \mapsto \exp(-x / 2)$ is $(-1/2) \exp(-x / 2)$. -/
theorem hasDerivAt_exp_neg_half (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) ((-1 / 2 : ℝ) * Real.exp (-x / 2)) x := by
  have h_inner : HasDerivAt (fun t : ℝ => (-1 / 2 : ℝ) * t) (-1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (-1 / 2 : ℝ)
  have h_exp := Real.hasDerivAt_exp ((-1 / 2 : ℝ) * x)
  have h_comp := h_exp.comp x h_inner
  have h_fun_eq : (Real.exp ∘ fun t : ℝ => -1 / 2 * t) = (fun t : ℝ => Real.exp (-t / 2)) := by
    funext t
    dsimp
    ring
  have h_arg_eq : -1 / 2 * x = -x / 2 := by ring
  have h_val_eq : Real.exp (-1 / 2 * x) * (-1 / 2) = (-1 / 2 : ℝ) * Real.exp (-x / 2) := by
    rw [h_arg_eq]
    ring
  rw [h_fun_eq, h_val_eq] at h_comp
  exact h_comp

/-- Derivative of `T_tail` is precisely $- K_{\text{kernel}}(x)$ for all $x > 0$. -/
theorem hasDerivAt_T_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt T_tail (- K_kernel x) x := by
  have h_u_pos : 0 < Real.exp (-x / 2) := Real.exp_pos (-x / 2)
  have h_u_lt_one : Real.exp (-x / 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_u_mem : Real.exp (-x / 2) ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, h_u_lt_one⟩
  have h_artanh := hasDerivAt_artanh h_u_mem
  have h_exp := hasDerivAt_exp_neg_half x
  have h_artanh_comp := h_artanh.comp x h_exp
  have h_arctan := Real.hasDerivAt_arctan (Real.exp (-x / 2))
  have h_arctan_comp := h_arctan.comp x h_exp
  have h_sum := h_artanh_comp.add h_arctan_comp
  have h_two := HasDerivAt.const_mul (2 : ℝ) h_sum
  change HasDerivAt T_tail (2 *
    (1 / (1 - Real.exp (-x / 2) ^ 2) * (-1 / 2 * Real.exp (-x / 2)) +
      1 / (1 + Real.exp (-x / 2) ^ 2) * (-1 / 2 * Real.exp (-x / 2)))) x at h_two
  have h_exp_sq : (Real.exp (-x / 2)) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h_exp_four : (Real.exp (-x / 2)) ^ 4 = Real.exp (-2 * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h_algebra : 2 * ((1 / (1 - Real.exp (-x / 2) ^ 2)) * ((-1 / 2) * Real.exp (-x / 2)) +
      (1 / (1 + Real.exp (-x / 2) ^ 2)) * ((-1 / 2) * Real.exp (-x / 2))) =
      - (2 * Real.exp (-x / 2)) / (1 - Real.exp (-2 * x)) := by
    rw [h_exp_sq]
    have h_denom_factor : 1 - Real.exp (-2 * x) = (1 - Real.exp (-x)) * (1 + Real.exp (-x)) := by
      rw [← h_exp_four, ← h_exp_sq]
      ring
    rw [h_denom_factor]
    have h_ne_minus : 1 - Real.exp (-x) ≠ 0 := by
      have : Real.exp (-x) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      linarith
    have h_ne_plus : 1 + Real.exp (-x) ≠ 0 := by
      have : 0 < Real.exp (-x) := Real.exp_pos (-x)
      linarith
    field_simp
    ring
  rw [h_algebra] at h_two
  have h_k_eq := K_kernel_eq x hx
  unfold K_kernel_alt at h_k_eq
  have h_neg_k : - (2 * Real.exp (-x / 2)) / (1 - Real.exp (-2 * x)) = - K_kernel x := by
    rw [h_k_eq]
    ring
  rw [h_neg_k] at h_two
  exact h_two

/-- Asymptotic vanishing of `T_tail x` as $x \to +\infty$: $\lim_{x \to \infty} T_{\text{tail}}(x) = 0$. -/
theorem tendsto_T_tail_atTop : Tendsto T_tail atTop (𝓝 0) := by
  have h_inner : Tendsto (fun x : ℝ => -x / 2) atTop atBot := by
    have h_eq : (fun x : ℝ => -x / 2) = (fun x : ℝ => (-1 / 2 : ℝ) * x) := by
      funext x; ring
    rw [h_eq]
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h_exp : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_inner
  have h_artanh_zero_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h_artanh_deriv := hasDerivAt_artanh h_artanh_zero_mem
  have h_artanh_cont : ContinuousAt Real.artanh 0 := h_artanh_deriv.continuousAt
  have h_artanh_lim : Tendsto Real.artanh (𝓝 0) (𝓝 0) := by
    have := h_artanh_cont.tendsto
    rw [Real.artanh_zero] at this
    exact this
  have h_artanh_comp : Tendsto (fun x : ℝ => Real.artanh (Real.exp (-x / 2))) atTop (𝓝 0) :=
    h_artanh_lim.comp h_exp
  have h_arctan_cont : ContinuousAt Real.arctan 0 := Real.continuous_arctan.continuousAt
  have h_arctan_lim : Tendsto Real.arctan (𝓝 0) (𝓝 0) := by
    have := h_arctan_cont.tendsto
    rw [Real.arctan_zero] at this
    exact this
  have h_arctan_comp : Tendsto (fun x : ℝ => Real.arctan (Real.exp (-x / 2))) atTop (𝓝 0) :=
    h_arctan_lim.comp h_exp
  have h_sum := h_artanh_comp.add h_arctan_comp
  have h_two := h_sum.const_mul (2 : ℝ)
  simp only [add_zero, mul_zero] at h_two
  exact h_two

/-! ## Part 3: Integrability and Integral Equality on Semi-Infinite Intervals -/

/-- Integrability of the Archimedean kernel $K(x)$ on the open ray $(b, \infty)$ for $b > 0$.
  Derived via FTC-2 integrability of nonpositive derivative with finite limit at infinity. -/
theorem integrableOn_Ioi_K_kernel {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn K_kernel (Ioi b) := by
  have hcont : ContinuousWithinAt T_tail (Ici b) b :=
    (hasDerivAt_T_tail hb).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi b, HasDerivAt T_tail (- K_kernel x) x :=
    fun x hx => hasDerivAt_T_tail (lt_trans hb hx)
  have hg'neg : ∀ x ∈ Ioi b, - K_kernel x ≤ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hb hx
    have h_sinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx_pos
    have h_exp_pos : 0 < Real.exp (x / 2) := Real.exp_pos (x / 2)
    have h_k_pos : 0 < K_kernel x := div_pos h_exp_pos h_sinh_pos
    linarith
  have h_int_neg := MeasureTheory.integrableOn_Ioi_deriv_of_nonpos hcont hderiv hg'neg tendsto_T_tail_atTop
  exact MeasureTheory.integrable_neg_iff.mp h_int_neg

/-- **Fundamental Tail Integral Theorem (Open Ray)**:
  For any $b > 0$, the improper integral of $K(x)$ over $(b, \infty)$ equals $T(b)$:
  $$\int_{(b, \infty)} K(x) \, dx = T(b) = 2(\operatorname{artanh}(e^{-b/2}) + \arctan(e^{-b/2})).$$ -/
theorem integral_Ioi_K_kernel_eq_T_tail {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi b, K_kernel x = T_tail b := by
  have hcont : ContinuousWithinAt T_tail (Ici b) b :=
    (hasDerivAt_T_tail hb).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi b, HasDerivAt T_tail (- K_kernel x) x :=
    fun x hx => hasDerivAt_T_tail (lt_trans hb hx)
  have hg'neg : ∀ x ∈ Ioi b, - K_kernel x ≤ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hb hx
    have h_sinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx_pos
    have h_exp_pos : 0 < Real.exp (x / 2) := Real.exp_pos (x / 2)
    have h_k_pos : 0 < K_kernel x := div_pos h_exp_pos h_sinh_pos
    linarith
  have h_ftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hg'neg tendsto_T_tail_atTop
  simp only [zero_sub] at h_ftc
  rw [MeasureTheory.integral_neg] at h_ftc
  linarith

/-- **Fundamental Tail Integral Theorem (Closed Ray)**:
  For any $b > 0$, the integral of $K(x)$ over $[b, \infty)$ is identically equal to $T(b)$,
  as the singleton boundary $\{b\}$ has Lebesgue measure zero:
  $$\int_{[b, \infty)} K(x) \, dx = T(b).$$ -/
theorem integral_Ici_K_kernel_eq_T_tail {b : ℝ} (hb : 0 < b) :
    ∫ x in Ici b, K_kernel x = T_tail b := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  exact integral_Ioi_K_kernel_eq_T_tail hb

end RH_Rebaseline

/-! ==========================================================================
  PART B: Gamma Fourier Bridge (From Task 0060 / GammaFourierBridge.lean)
  ========================================================================== -/

/-
Released under Apache 2.0 license.
-/


open MeasureTheory Set Filter Real
open scoped Topology ComplexConjugate
open Complex

namespace RH_GammaSqrtBound

/-! ## Part 1: Core Definitions and Gamma Series Baseline (X1 Integration) -/

/-- The n-th term of the Gamma difference series:
$$ \operatorname{gammaTerm}(t, n) = \frac{1}{n + 1/4} - \frac{n + 1/4}{(n + 1/4)^2 + t^2 / 4} $$
-/
noncomputable def gammaTerm (t : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1 / 4) - ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4)

/-- Nonnegativity of each term in the Gamma difference series:
$$ \forall t \in \mathbb{R}, \forall n \in \mathbb{N}, \quad \operatorname{gammaTerm}(t, n) \ge 0 $$
-/
theorem gammaTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ gammaTerm t n := by
  unfold gammaTerm
  have hu : 0 < (n : ℝ) + 1 / 4 := by
    have h1 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < 1 / 4 := by norm_num
    linarith
  have hu2 : 0 < ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by
    have hu_sq : 0 < ((n : ℝ) + 1 / 4) ^ 2 := sq_pos_of_pos hu
    have ht_sq : 0 ≤ t ^ 2 / 4 := by positivity
    linarith
  have h_eq : 1 / ((n : ℝ) + 1 / 4) - ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) =
      (t ^ 2 / 4) / (((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4)) := by
    have hu_ne : (n : ℝ) + 1 / 4 ≠ 0 := hu.ne'
    have hdenom_ne : ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 ≠ 0 := hu2.ne'
    field_simp
    ring
  rw [h_eq]
  positivity

/-- Real part of complex exponential with argument $(-2u + it)x$. -/
theorem re_exp_mul (u t x : ℝ) :
    (Complex.exp ((((-2 * u : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)) * (x : ℂ))).re =
    Real.exp (-2 * u * x) * Real.cos (t * x) := by
  have h_arg : ((((-2 * u : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)) * (x : ℂ)) =
      (((-2 * u * x : ℝ) : ℂ) + Complex.I * ((t * x : ℝ) : ℂ)) := by
    push_cast; ring
  rw [h_arg, Complex.exp_re]
  have hre : (((-2 * u * x : ℝ) : ℂ) + Complex.I * ((t * x : ℝ) : ℂ)).re = -2 * u * x := by simp
  have him : (((-2 * u * x : ℝ) : ℂ) + Complex.I * ((t * x : ℝ) : ℂ)).im = t * x := by simp
  rw [hre, him]

/-- Real part of the reciprocal of a general complex number $a + i b$. -/
theorem re_inv (a b : ℝ) :
    ((1 : ℂ) / (((a : ℝ) : ℂ) + Complex.I * ((b : ℝ) : ℂ))).re = a / (a ^ 2 + b ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : (((a : ℝ) : ℂ) + Complex.I * ((b : ℝ) : ℂ)).re = a := by simp
  have him : (((a : ℝ) : ℂ) + Complex.I * ((b : ℝ) : ℂ)).im = b := by simp
  rw [Complex.normSq_apply, hre, him]
  ring

/-- Integrability of the decaying exponential $x \mapsto e^{-2ux}$ on $(0, \infty)$ for $u > 0$. -/
theorem integrableOn_exp_neg_two_u {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun x : ℝ => Real.exp (-2 * u * x)) (Ioi 0) := by
  have ha : -2 * u < 0 := by linarith
  exact integrableOn_exp_mul_Ioi ha 0

/-- Integrability of the product $x \mapsto e^{-2ux}\cos(tx)$ on $(0, \infty)$ for $u > 0$. -/
theorem integrableOn_exp_cos {u t : ℝ} (hu : 0 < u) :
    IntegrableOn (fun x : ℝ => Real.exp (-2 * u * x) * Real.cos (t * x)) (Ioi 0) := by
  set a : ℂ := (((-2 * u : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ))
  have ha_re : a.re < 0 := by
    have hre : a.re = -2 * u := by simp [a]
    rw [hre]; linarith
  have h_int_c := integrableOn_exp_mul_complex_Ioi ha_re 0
  have h_eq_fun : (fun x : ℝ => Real.exp (-2 * u * x) * Real.cos (t * x)) =
      (fun x : ℝ => (Complex.exp (a * (x : ℂ))).re) := by
    funext x
    exact (re_exp_mul u t x).symm
  rw [h_eq_fun]
  exact h_int_c.re

/-- Integrability of the integrand $x \mapsto e^{-2ux}(1 - \cos(tx))$ on $(0, \infty)$ for $u > 0$. -/
theorem integrableOn_exp_one_sub_cos {u t : ℝ} (hu : 0 < u) :
    IntegrableOn (fun x : ℝ => Real.exp (-2 * u * x) * (1 - Real.cos (t * x))) (Ioi 0) := by
  have h_eq : (fun x : ℝ => Real.exp (-2 * u * x) * (1 - Real.cos (t * x))) =
      (fun x => Real.exp (-2 * u * x) - Real.exp (-2 * u * x) * Real.cos (t * x)) := by
    funext x; ring
  rw [h_eq]
  exact (integrableOn_exp_neg_two_u hu).sub (integrableOn_exp_cos hu)

/-- Laplace transform evaluation of $x \mapsto e^{-2ux}\cos(tx)$ on $(0, \infty)$:
$$ \int_0^\infty e^{-2ux} \cos(tx) dx = \frac{2u}{(2u)^2 + t^2} $$
-/
theorem integral_exp_cos (u t : ℝ) (hu : 0 < u) :
    ∫ x in Ioi 0, Real.exp (-2 * u * x) * Real.cos (t * x) =
    (2 * u) / ((2 * u) ^ 2 + t ^ 2) := by
  set a : ℂ := (((-2 * u : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ))
  have ha_re : a.re < 0 := by
    have hre : a.re = -2 * u := by simp [a]
    rw [hre]; linarith
  have h_int_c := integrableOn_exp_mul_complex_Ioi ha_re 0
  have h_eq_fun : (fun x : ℝ => Real.exp (-2 * u * x) * Real.cos (t * x)) =
      (fun x : ℝ => RCLike.re (Complex.exp (a * (x : ℂ)))) := by
    funext x
    exact (re_exp_mul u t x).symm
  rw [h_eq_fun]
  rw [integral_re h_int_c]
  have h_c_val := integral_exp_mul_complex_Ioi ha_re 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h_c_val
  rw [h_c_val]
  have h_cast : RCLike.re (-1 / a) = (-1 / a).re := rfl
  rw [h_cast]
  have h_div : (-1 / a) = - (1 / a) := by ring
  rw [h_div, Complex.neg_re]
  have h_inv : (1 / a).re = (-2 * u) / ((-2 * u) ^ 2 + t ^ 2) := by
    exact re_inv (-2 * u) t
  rw [h_inv]
  ring

/-- Laplace transform evaluation of $x \mapsto e^{-2ux}$ on $(0, \infty)$:
$$ \int_0^\infty e^{-2ux} dx = \frac{1}{2u} $$
-/
theorem integral_exp_neg_two_u (u : ℝ) (hu : 0 < u) :
    ∫ x in Ioi 0, Real.exp (-2 * u * x) = 1 / (2 * u) := by
  have ha : -2 * u < 0 := by linarith
  have h := integral_exp_mul_Ioi ha 0
  simp only [mul_zero, Real.exp_zero] at h
  rw [h]
  have : - (1 : ℝ) / (-2 * u) = 1 / (2 * u) := by ring
  exact this

/-- Laplace transform of the kernel $x \mapsto e^{-2ux}(1 - \cos(tx))$:
$$ \int_0^\infty e^{-2ux} (1 - \cos(tx)) dx = \frac{1}{2u} - \frac{2u}{(2u)^2 + t^2} $$
-/
theorem integral_exp_one_sub_cos (u t : ℝ) (hu : 0 < u) :
    ∫ x in Ioi 0, Real.exp (-2 * u * x) * (1 - Real.cos (t * x)) =
    1 / (2 * u) - (2 * u) / ((2 * u) ^ 2 + t ^ 2) := by
  have h_eq : (fun x : ℝ => Real.exp (-2 * u * x) * (1 - Real.cos (t * x))) =
      (fun x => Real.exp (-2 * u * x) - Real.exp (-2 * u * x) * Real.cos (t * x)) := by
    funext x; ring
  rw [h_eq]
  rw [integral_sub (integrableOn_exp_neg_two_u hu) (integrableOn_exp_cos hu)]
  rw [integral_exp_neg_two_u u hu, integral_exp_cos u t hu]

/-- Laplace Integral Representation of the Gamma Difference Terms:
$$ \operatorname{gammaTerm}(t, n) = 2 \int_{0}^\infty e^{-2(n + 1/4)x} (1 - \cos(tx)) \, dx $$
-/
theorem gammaTerm_eq_two_integral (t : ℝ) (n : ℕ) :
    gammaTerm t n =
    2 * ∫ x in Ioi 0, Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x)) := by
  have hu : 0 < (n : ℝ) + 1 / 4 := by
    have h1 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < 1 / 4 := by norm_num
    linarith
  rw [integral_exp_one_sub_cos ((n : ℝ) + 1 / 4) t hu]
  unfold gammaTerm
  have hu2_pos : 0 < ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by
    have hu_sq : 0 < ((n : ℝ) + 1 / 4) ^ 2 := sq_pos_of_pos hu
    have ht_sq : 0 ≤ t ^ 2 / 4 := by positivity
    linarith
  have h_denom : (2 * ((n : ℝ) + 1 / 4)) ^ 2 + t ^ 2 = 4 * (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by ring
  rw [h_denom]
  have hu_ne : (n : ℝ) + 1 / 4 ≠ 0 := hu.ne'
  have hu2_ne : ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 ≠ 0 := hu2_pos.ne'
  field_simp
  ring

/-! ## Part 2: HasSum Digamma Difference Series (from Zeta23) -/

/-- Points with real part 1/4 avoid all integers. -/
theorem mem_integerComplement_quarter (y : ℝ) :
    ((1/4 : ℝ) : ℂ) + Complex.I * (y : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.intCast_re] at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; norm_num
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; norm_num
    exact_mod_cast h
  omega

/-- The base point 1/4 avoids all integers. -/
theorem mem_integerComplement_quarter_real :
    ((1/4 : ℝ) : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp only [Complex.ofReal_re, Complex.intCast_re] at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; norm_num
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; norm_num
    exact_mod_cast h
  omega

theorem re_inv_real (a : ℝ) :
    ((1 : ℂ) / (((a : ℝ) : ℂ))).re = 1 / a := by
  have : ((1 : ℂ) / (((a : ℝ) : ℂ))) = ((((1 / a : ℝ)) : ℂ)) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

theorem re_gamma_term_step (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / (((1/4 : ℝ) : ℂ) + (n : ℂ) + 1) - (1 : ℂ) / (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) + (n : ℂ) + 1)).re =
    gammaTerm t (n + 1) := by
  rw [Complex.sub_re]
  have h1 : ((1/4 : ℝ) : ℂ) + (n : ℂ) + 1 = ((((n + 1 : ℝ) + 1/4 : ℝ)) : ℂ) := by
    push_cast; ring
  have h2 : ((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) + (n : ℂ) + 1 =
      ((((n + 1 : ℝ) + 1/4 : ℝ)) : ℂ) + Complex.I * (((t / 2 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [h1, h2]
  rw [re_inv_real, re_inv]
  unfold gammaTerm
  have ht : (t / 2) ^ 2 = t ^ 2 / 4 := by ring
  rw [ht]
  have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_add_one n
  rw [h_cast]

theorem re_inv_diff_zero (t : ℝ) :
    ((1 : ℂ) / (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    ((1 : ℂ) / (((1/4 : ℝ) : ℂ))).re =
    - gammaTerm t 0 := by
  rw [re_inv, re_inv_real]
  unfold gammaTerm
  have ht : (t / 2) ^ 2 = t ^ 2 / 4 := by ring
  rw [ht]
  simp only [Nat.cast_zero, zero_add]
  ring

theorem hasSum_digamma_difference_shifted (t : ℝ) :
    HasSum (fun n : ℕ => gammaTerm t (n + 1))
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
       (Complex.digamma ((1/4 : ℝ) : ℂ)).re - gammaTerm t 0) := by
  set z : ℂ := ((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)
  set z0 : ℂ := ((1/4 : ℝ) : ℂ)
  have hz : z ∈ Complex.integerComplement := mem_integerComplement_quarter (t / 2)
  have hz0 : z0 ∈ Complex.integerComplement := mem_integerComplement_quarter_real
  have h1 := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have h2 := Zeta23.DigammaSeries.hasSum_digamma_series hz0
  have hsub := h1.sub h2
  have h_term : (fun b : ℕ => 1 / ((b : ℂ) + 1) - 1 / (z + (b : ℂ) + 1) - (1 / ((b : ℂ) + 1) - 1 / (z0 + (b : ℂ) + 1))) =
      (fun n : ℕ => 1 / (z0 + (n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1)) := by
    funext n; ring
  have h_sum : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z -
       (Complex.digamma z0 + (Real.eulerMascheroniConstant : ℂ) + 1 / z0)) =
      (Complex.digamma z - Complex.digamma z0 + 1 / z - 1 / z0) := by ring
  rw [h_term, h_sum] at hsub
  have hre := hsub.map Complex.reCLM Complex.continuous_re
  change HasSum (fun n : ℕ => ((1 : ℂ) / (z0 + (n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1)).re)
      (Complex.re (Complex.digamma z - Complex.digamma z0 + 1 / z - 1 / z0)) at hre
  have hre_term : (fun n : ℕ => ((1 : ℂ) / (z0 + (n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1)).re) =
      (fun n : ℕ => gammaTerm t (n + 1)) := by
    funext n
    exact re_gamma_term_step t n
  rw [hre_term] at hre
  have hval : (Complex.digamma z - Complex.digamma z0 + 1 / z - 1 / z0).re =
      (Complex.digamma z).re - (Complex.digamma z0).re - gammaTerm t 0 := by
    simp only [Complex.sub_re, Complex.add_re]
    have h_diff : (1 / z).re - (1 / z0).re = - gammaTerm t 0 := re_inv_diff_zero t
    linarith
  rwa [hval] at hre

/-- Complete Digamma Difference Series Representation:
$$ \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) = \sum_{n=0}^\infty \operatorname{gammaTerm}(t, n) $$
-/
theorem hasSum_digamma_difference (t : ℝ) :
    HasSum (fun n : ℕ => gammaTerm t n)
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
       (Complex.digamma ((1/4 : ℝ) : ℂ)).re) := by
  have hshift := hasSum_digamma_difference_shifted t
  have hfin := (hasSum_nat_add_iff (f := fun n => gammaTerm t n) 1).mp hshift
  rw [Finset.sum_range_one] at hfin
  have h_simp : ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
       (Complex.digamma ((1/4 : ℝ) : ℂ)).re - gammaTerm t 0) + gammaTerm t 0 =
       (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
       (Complex.digamma ((1/4 : ℝ) : ℂ)).re := by ring
  rwa [h_simp] at hfin

/-- HasSum identity for the sequence of Laplace integrals:
$$ \sum_{n=0}^\infty 2 \int_0^\infty e^{-2(n+1/4)x}(1 - \cos(tx)) dx = \operatorname{Re}\psi(1/4+it/2) - \operatorname{Re}\psi(1/4) $$
-/
theorem hasSum_laplace_integrals (t : ℝ) :
    HasSum (fun n : ℕ => 2 * ∫ x in Ioi 0, Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x)))
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - (Complex.digamma ((1/4 : ℝ) : ℂ)).re) := by
  have h := hasSum_digamma_difference t
  have h_eq : (fun n : ℕ => 2 * ∫ x in Ioi 0, Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x))) =
      (fun n => gammaTerm t n) := by
    funext n
    exact (gammaTerm_eq_two_integral t n).symm
  rwa [h_eq]

/-! ## Part 3: Integrand Sequence and Summable Norms -/

/-- The integrand $F_n(t, x) = 2 e^{-2(n+1/4)x}(1 - \cos(tx))$. -/
noncomputable def F_term (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x))

/-- Pointwise nonnegativity of $F_n(t, x)$ for all $x$. -/
theorem F_term_nonneg (t : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ F_term t n x := by
  unfold F_term
  have h1 : 0 ≤ Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) := (Real.exp_pos _).le
  have h2 : 0 ≤ 1 - Real.cos (t * x) := by
    have := Real.cos_le_one (t * x)
    linarith
  positivity

/-- The norm of $F_n(t, x)$ equals $F_n(t, x)$ due to nonnegativity. -/
theorem norm_F_term_eq (t : ℝ) (n : ℕ) (x : ℝ) : ‖F_term t n x‖ = F_term t n x :=
  Real.norm_of_nonneg (F_term_nonneg t n x)

/-- Integrability of $F_n(t, \cdot)$ on $(0, \infty)$. -/
theorem integrableOn_F_term (t : ℝ) (n : ℕ) :
    IntegrableOn (F_term t n) (Ioi 0) := by
  have hu : 0 < (n : ℝ) + 1 / 4 := by
    have : (0 : ℝ) < 1 / 4 := by norm_num
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_int := integrableOn_exp_one_sub_cos hu (t := t)
  have h_mul := h_int.const_mul 2
  have h_eq : F_term t n = (fun x => 2 * (Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x)))) := by
    funext x
    unfold F_term
    ring
  rw [h_eq]
  exact h_mul

/-- Integral of the norm of $F_n$ equals the integral of $F_n$. -/
theorem integral_norm_F_term_eq (t : ℝ) (n : ℕ) :
    ∫ x in Ioi 0, ‖F_term t n x‖ = ∫ x in Ioi 0, F_term t n x := by
  congr 1; funext x
  exact norm_F_term_eq t n x

/-- The integral of $F_n(t, x)$ equals $\operatorname{gammaTerm}(t, n)$. -/
theorem integral_F_term_eq_gammaTerm (t : ℝ) (n : ℕ) :
    ∫ x in Ioi 0, F_term t n x = gammaTerm t n := by
  have h_eq : F_term t n = (fun x => 2 * (Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) * (1 - Real.cos (t * x)))) := by
    funext x
    unfold F_term
    ring
  rw [h_eq]
  rw [integral_const_mul]
  exact (gammaTerm_eq_two_integral t n).symm

/-- HasSum for the integrals of $F_n$ to the digamma difference. -/
theorem hasSum_integral_F_term_digamma (t : ℝ) :
    HasSum (fun n : ℕ => ∫ x in Ioi 0, F_term t n x)
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
       (Complex.digamma ((1/4 : ℝ) : ℂ)).re) := by
  have h := hasSum_digamma_difference t
  have h_eq : (fun n : ℕ => ∫ x in Ioi 0, F_term t n x) = (fun n => gammaTerm t n) := by
    funext n
    exact integral_F_term_eq_gammaTerm t n
  rwa [h_eq]

/-- The series of $L^1$ norms of $F_n$ is summable on $(0, \infty)$. -/
theorem summable_integral_norm_F_term (t : ℝ) :
    Summable (fun n : ℕ => ∫ x in Ioi 0, ‖F_term t n x‖) := by
  have h_hasSum := hasSum_integral_F_term_digamma t
  have h_summable := h_hasSum.summable
  have h_eq : (fun n : ℕ => ∫ x in Ioi 0, ‖F_term t n x‖) =
              (fun n : ℕ => ∫ x in Ioi 0, F_term t n x) := by
    funext n
    exact integral_norm_F_term_eq t n
  rwa [h_eq]

/-! ## Part 4: Dominated Convergence Series-Integral Interchange -/

/-- Dominated convergence termwise integration interchange:
The sum of integrals of $F_n$ converges to the integral of the pointwise sum $\sum' n, F_n$.
-/
theorem hasSum_integral_tsum_F_term (t : ℝ) :
    HasSum (fun n : ℕ => ∫ x in Ioi 0, F_term t n x)
      (∫ x in Ioi 0, ∑' n : ℕ, F_term t n x) := by
  have h_int : ∀ n : ℕ, Integrable (F_term t n) (Measure.restrict volume (Ioi 0)) :=
    fun n => integrableOn_F_term t n
  have h_sum : Summable (fun n : ℕ => ∫ x in Ioi 0, ‖F_term t n x‖) :=
    summable_integral_norm_F_term t
  exact hasSum_integral_of_summable_integral_norm h_int h_sum

/-- Equality between the Digamma difference and the integral of $\sum' n, F_n(t, x)$:
$$ \operatorname{Re}\psi(1/4+it/2) - \operatorname{Re}\psi(1/4) = \int_0^\infty \left(\sum_{n=0}^\infty F_n(t, x)\right) dx $$
by uniqueness of limits in `HasSum`.
-/
theorem digamma_diff_eq_integral_tsum (t : ℝ) :
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    (Complex.digamma ((1/4 : ℝ) : ℂ)).re =
    ∫ x in Ioi 0, ∑' n : ℕ, F_term t n x := by
  have h1 := hasSum_integral_F_term_digamma t
  have h2 := hasSum_integral_tsum_F_term t
  exact h1.unique h2

/-! ## Part 5: Geometric Series Summation and Archimedean Kernel -/

/-- Exponential decomposition: $e^{-2(n+1/4)x} = e^{-x/2} (e^{-2x})^n$. -/
theorem exp_decomp (n : ℕ) (x : ℝ) :
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * x) = Real.exp (-x / 2) * (Real.exp (-2 * x)) ^ n := by
  have h_exp : -2 * ((n : ℝ) + 1 / 4) * x = -x / 2 + (n : ℝ) * (-2 * x) := by ring
  rw [h_exp, Real.exp_add, Real.exp_nat_mul]

/-- Archimedean kernel in hyperbolic form:
  `K_kernel x = exp(x / 2) / sinh x`. -/
noncomputable def K_kernel (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sinh x

/-- Archimedean kernel in exponential fraction form:
  `K_kernel_alt x = 2 exp(-x / 2) / (1 - exp(-2x))`. -/
noncomputable def K_kernel_alt (x : ℝ) : ℝ :=
  2 * Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

/-- Equivalence of the two representations of the Archimedean kernel for $x > 0$. -/
theorem K_kernel_eq (x : ℝ) (_hx : 0 < x) :
    K_kernel x = K_kernel_alt x := by
  unfold K_kernel K_kernel_alt
  rw [Real.sinh_eq]
  have h_exp_neg_mul : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    have h_zero : x + -x = 0 := by ring
    rw [h_zero]
    exact Real.exp_zero
  have h_num : 2 * Real.exp (x / 2) * Real.exp (-x) = 2 * Real.exp (-x / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have h_denom : (Real.exp x - Real.exp (-x)) * Real.exp (-x) = 1 - Real.exp (-2 * x) := by
    rw [sub_mul, h_exp_neg_mul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have h_div_two : Real.exp (x / 2) / ((Real.exp x - Real.exp (-x)) / 2) =
      2 * Real.exp (x / 2) / (Real.exp x - Real.exp (-x)) := by
    rw [div_div_eq_mul_div]
    ring
  rw [h_div_two]
  rw [← h_num, ← h_denom]
  exact (mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos (-x)))).symm

/-- Geometric series evaluation for ratio $e^{-2x} < 1$ when $x > 0$. -/
theorem geom_sum_exp {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (Real.exp (-2 * x)) ^ n) (1 / (1 - Real.exp (-2 * x))) := by
  have h_pos : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have h_lt : Real.exp (-2 * x) < 1 := by
    have : -2 * x < 0 := by linarith
    have h_exp := Real.exp_lt_exp.mpr this
    rw [Real.exp_zero] at h_exp
    exact h_exp
  have h_geom := hasSum_geometric_of_lt_one h_pos h_lt
  rw [one_div]
  exact h_geom

/-- Factoring $F_n(t, x)$ into prefactor and geometric ratio term. -/
theorem F_term_eq_factor (t : ℝ) (n : ℕ) (x : ℝ) :
    F_term t n x = (2 * Real.exp (-x / 2) * (1 - Real.cos (t * x))) * (Real.exp (-2 * x)) ^ n := by
  unfold F_term
  rw [exp_decomp n x]
  ring

/-- Sum of $F_n(t, x)$ equals $(1 - \cos(tx)) K(x)$ for each $x > 0$ in `HasSum` form. -/
theorem hasSum_F_term (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => F_term t n x) ((1 - Real.cos (t * x)) * K_kernel x) := by
  have h_geom := geom_sum_exp hx
  have h_mul := h_geom.mul_left (2 * Real.exp (-x / 2) * (1 - Real.cos (t * x)))
  have h_fun : (fun n : ℕ => (2 * Real.exp (-x / 2) * (1 - Real.cos (t * x))) * (Real.exp (-2 * x)) ^ n) =
      (fun n : ℕ => F_term t n x) := by
    funext n
    exact (F_term_eq_factor t n x).symm
  rw [h_fun] at h_mul
  have h_val : (2 * Real.exp (-x / 2) * (1 - Real.cos (t * x))) * (1 / (1 - Real.exp (-2 * x))) =
      (1 - Real.cos (t * x)) * K_kernel x := by
    rw [K_kernel_eq x hx]
    unfold K_kernel_alt
    ring
  rwa [h_val] at h_mul

/-- Pointwise sum identity $\sum' n, F_n(t, x) = (1 - \cos(tx)) K(x)$ for $x > 0$. -/
theorem tsum_F_term_eq (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, F_term t n x) = (1 - Real.cos (t * x)) * K_kernel x :=
  (hasSum_F_term t hx).tsum_eq

/-- Almost-everywhere equality on $(0, \infty)$ with respect to Lebesgue measure. -/
theorem ae_eq_tsum_K_kernel (t : ℝ) :
    (fun x => ∑' n : ℕ, F_term t n x) =ᵐ[volume.restrict (Ioi 0)]
    (fun x => (1 - Real.cos (t * x)) * K_kernel x) := by
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro x hx
  exact tsum_F_term_eq t hx

/-- Integral of the pointwise sum equals the kernel integral on $(0, \infty)$. -/
theorem integral_tsum_eq_integral_kernel (t : ℝ) :
    ∫ x in Ioi 0, (∑' n : ℕ, F_term t n x) =
    ∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x :=
  integral_congr_ae (ae_eq_tsum_K_kernel t)

/-- **Main Theorem (Gamma Kernel Integral Representation)**:
For any $t \in \mathbb{R}$,
$$ \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) = \int_0^\infty (1 - \cos(tx)) K(x) \, dx $$
where $K(x) = \frac{e^{x/2}}{\sinh x}$.
-/
theorem digamma_diff_eq_kernel_integral (t : ℝ) :
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    (Complex.digamma ((1/4 : ℝ) : ℂ)).re =
    ∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x := by
  rw [digamma_diff_eq_integral_tsum t]
  exact integral_tsum_eq_integral_kernel t

/-! ## Part 6: Integrability and Positivity (X1 Integration) -/

/-- Strict positivity of the Digamma difference for $t \ne 0$. -/
theorem digamma_diff_pos {t : ℝ} (ht : t ≠ 0) :
    0 < (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - (Complex.digamma ((1/4 : ℝ) : ℂ)).re := by
  have hn : 0 ≤ ∑' n : ℕ, gammaTerm t (n + 1) := tsum_nonneg (fun n => gammaTerm_nonneg t (n + 1))
  rw [(hasSum_digamma_difference_shifted t).tsum_eq] at hn
  have hden : (1 : ℝ) + 4 * t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have heq : gammaTerm t 0 = 16 * t ^ 2 / (1 + 4 * t ^ 2) := by
    unfold gammaTerm
    simp only [Nat.cast_zero, zero_add]
    field_simp
    ring
  have hp : 0 < gammaTerm t 0 := by
    rw [heq]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ht)) (by positivity)
  linarith

/-- Integrability of the kernel product $(1 - \cos(tx)) K(x)$ on $(0, \infty)$ for all real $t$. -/
theorem integrableOn_kernel_product (t : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (t * x)) * K_kernel x) (Ioi 0) := by
  by_cases ht : t = 0
  · subst t
    simp
  · apply Integrable.of_integral_ne_zero
    rw [← digamma_diff_eq_kernel_integral t]
    exact ne_of_gt (digamma_diff_pos ht)

/-! ## Part 7: Trigonometric Bounds on 1 - cos u (X3) -/

/-- Nonnegativity: $0 \le 1 - \cos u$. -/
theorem one_sub_cos_nonneg (u : ℝ) : 0 ≤ 1 - Real.cos u := by
  have := Real.cos_le_one u
  linarith

/-- Constant bound: $1 - \cos u \le 2$. -/
theorem one_sub_cos_le_two (u : ℝ) : 1 - Real.cos u ≤ 2 := by
  have := Real.neg_one_le_cos u
  linarith

/-- Lipschitz bound: $1 - \cos u \le |u|$. -/
theorem one_sub_cos_le_abs (u : ℝ) : 1 - Real.cos u ≤ |u| := by
  have h := Real.abs_cos_sub_cos_le u 0
  rw [Real.cos_zero, sub_zero] at h
  have h_eq : |Real.cos u - 1| = 1 - Real.cos u := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (one_sub_cos_nonneg u)
  rwa [h_eq] at h

/-- Global square-root bound: $1 - \cos u \le 2 \sqrt{|u|}$ for all $u \in \mathbb{R}$. -/
theorem one_sub_cos_le_two_sqrt_abs (u : ℝ) : 1 - Real.cos u ≤ 2 * Real.sqrt |u| := by
  by_cases h : |u| ≤ 1
  · have h_le := one_sub_cos_le_abs u
    have h_sq : |u| ^ 2 ≤ |u| := by
      have hu_pos : 0 ≤ |u| := abs_nonneg u
      have : |u| * |u| ≤ |u| * 1 := mul_le_mul_of_nonneg_left h hu_pos
      rw [mul_one, ← sq] at this
      exact this
    have h_sqrt : |u| ≤ Real.sqrt |u| := by
      have hu_pos : 0 ≤ |u| := abs_nonneg u
      have h1 := Real.sqrt_le_sqrt h_sq
      rw [Real.sqrt_sq hu_pos] at h1
      exact h1
    have h_two : Real.sqrt |u| ≤ 2 * Real.sqrt |u| := by
      have : 0 ≤ Real.sqrt |u| := Real.sqrt_nonneg |u|
      linarith
    linarith
  · have h_gt : 1 < |u| := not_le.mp h
    have h_two := one_sub_cos_le_two u
    have h_sqrt_gt : 1 < Real.sqrt |u| := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) h_gt
    have h_two_lt : 2 < 2 * Real.sqrt |u| := by linarith
    linarith

/-- Factored bound: for $x > 0$, $1 - \cos(tx) \le 2 \sqrt{|t|} \sqrt{x}$. -/
theorem one_sub_cos_mul_le_two_sqrt_mul (t : ℝ) {x : ℝ} (hx : 0 < x) :
    1 - Real.cos (t * x) ≤ 2 * Real.sqrt |t| * Real.sqrt x := by
  have h := one_sub_cos_le_two_sqrt_abs (t * x)
  rw [abs_mul, Real.sqrt_mul (abs_nonneg t)] at h
  have hx_abs : |x| = x := abs_of_pos hx
  rw [hx_abs] at h
  calc 1 - Real.cos (t * x) ≤ 2 * (Real.sqrt |t| * Real.sqrt x) := h
    _ = 2 * Real.sqrt |t| * Real.sqrt x := by ring

/-! ## Part 8: Kernel Pointwise Bound and Integrability (X2) -/

/-- Archimedean kernel upper bound on exponential form:
$K_{\text{alt}}(x) \le e^{-x/2} (2 + 1/x)$ for $x > 0$.
-/
theorem K_kernel_alt_le_bound (x : ℝ) (hx : 0 < x) :
    K_kernel_alt x ≤ Real.exp (-x / 2) * (2 + 1 / x) := by
  have h_exp_ge : 2 * x + 1 ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)
  have h_pos_exp : 0 < Real.exp (-2 * x) := Real.exp_pos (-2 * x)
  have h_mul_exp : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
    rw [← Real.exp_add]
    have : 2 * x + -2 * x = 0 := by ring
    rw [this, Real.exp_zero]
  have h_step1 : (2 * x + 1) * Real.exp (-2 * x) ≤ 1 := by
    calc (2 * x + 1) * Real.exp (-2 * x) ≤ Real.exp (2 * x) * Real.exp (-2 * x) :=
          mul_le_mul_of_nonneg_right h_exp_ge h_pos_exp.le
      _ = 1 := h_mul_exp
  have h_step2 : 2 * x ≤ (2 * x + 1) * (1 - Real.exp (-2 * x)) := by
    calc 2 * x = (2 * x + 1) - 1 := by ring
      _ ≤ (2 * x + 1) - (2 * x + 1) * Real.exp (-2 * x) := by linarith [h_step1]
      _ = (2 * x + 1) * (1 - Real.exp (-2 * x)) := by ring
  have h_d1 : 0 < 1 - Real.exp (-2 * x) := by
    have : -2 * x < 0 := by linarith
    have h_lt : Real.exp (-2 * x) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr this
    linarith
  have h_div : 2 / (1 - Real.exp (-2 * x)) ≤ (2 + 1 / x) := by
    have h_x_ne : x ≠ 0 := hx.ne'
    have h_d1_ne : 1 - Real.exp (-2 * x) ≠ 0 := h_d1.ne'
    have h_equiv : (2 : ℝ) / (1 - Real.exp (-2 * x)) ≤ (2 * x + 1) / x := by
      rw [div_le_div_iff₀ h_d1 hx]
      linarith [h_step2]
    have h_id : (2 * x + 1) / x = 2 + 1 / x := by
      field_simp
    rwa [h_id] at h_equiv
  unfold K_kernel_alt
  have h_exp_half_pos : 0 ≤ Real.exp (-x / 2) := (Real.exp_pos _).le
  calc 2 * Real.exp (-x / 2) / (1 - Real.exp (-2 * x))
      = Real.exp (-x / 2) * (2 / (1 - Real.exp (-2 * x))) := by ring
    _ ≤ Real.exp (-x / 2) * (2 + 1 / x) := mul_le_mul_of_nonneg_left h_div h_exp_half_pos

/-- Pointwise upper bound for $K(x)$ on $(0, \infty)$: $K(x) \le e^{-x/2} (2 + 1/x)$. -/
theorem K_kernel_le_bound (x : ℝ) (hx : 0 < x) :
    K_kernel x ≤ Real.exp (-x / 2) * (2 + 1 / x) := by
  rw [K_kernel_eq x hx]
  exact K_kernel_alt_le_bound x hx

/-- Pointwise nonnegativity of $K(x)$ for $x > 0$. -/
theorem K_kernel_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ K_kernel x := by
  unfold K_kernel
  have h1 : 0 < Real.exp (x / 2) := Real.exp_pos _
  have h2 : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  exact div_nonneg h1.le h2.le

/-- Pointwise nonnegativity of $\sqrt{x} K(x)$ for $x > 0$. -/
theorem sqrt_mul_K_kernel_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.sqrt x * K_kernel x :=
  mul_nonneg (Real.sqrt_nonneg x) (K_kernel_nonneg x hx)

/-- Integrable component 1: $x \mapsto x^{1/2} e^{-(1/2) x}$ on $(0, \infty)$. -/
theorem integrable_rpow_half :
    IntegrableOn (fun x : ℝ => x ^ (1/2 : ℝ) * Real.exp (- (1/2 : ℝ) * x ^ (1 : ℝ))) (Ioi 0) := by
  have hs : (-1 : ℝ) < 1 / 2 := by norm_num
  have hp : (0 : ℝ) < (1 : ℝ) := by norm_num
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs hp hb

/-- Integrable component 2: $x \mapsto x^{-1/2} e^{-(1/2) x}$ on $(0, \infty)$. -/
theorem integrable_rpow_neg_half :
    IntegrableOn (fun x : ℝ => x ^ (-1/2 : ℝ) * Real.exp (- (1/2 : ℝ) * x ^ (1 : ℝ))) (Ioi 0) := by
  have hs : (-1 : ℝ) < -1 / 2 := by norm_num
  have hp : (0 : ℝ) < (1 : ℝ) := by norm_num
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs hp hb

/-- Integrability of the upper bound envelope $e^{-x/2}(2\sqrt{x} + x^{-1/2})$ on $(0, \infty)$. -/
theorem integrableOn_sqrt_envelope :
    IntegrableOn (fun x : ℝ => 2 * (x ^ (1/2 : ℝ) * Real.exp (- (1/2 : ℝ) * x ^ (1 : ℝ))) +
                                (x ^ (-1/2 : ℝ) * Real.exp (- (1/2 : ℝ) * x ^ (1 : ℝ)))) (Ioi 0) :=
  (integrable_rpow_half.const_mul 2).add integrable_rpow_neg_half

/-- Definition of the finite constant $C_K = \int_0^\infty \sqrt{x} K(x) dx$. -/
noncomputable def C_K : ℝ :=
  ∫ x in Ioi 0, Real.sqrt x * K_kernel x

/-- Nonnegativity of the constant $C_K$. -/
theorem C_K_nonneg : 0 ≤ C_K := by
  unfold C_K
  apply integral_nonneg_of_ae
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro x hx
  exact sqrt_mul_K_kernel_nonneg x hx

/-! ## Part 9: Global Square-Root Bounds for the Digamma Difference (X3) -/

/-- Nonnegativity of the Digamma difference for all real $t$. -/
theorem digamma_diff_nonneg (t : ℝ) :
    0 ≤ (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re := by
  by_cases ht : t = 0
  · subst t
    simp
  · exact (digamma_diff_pos ht).le

/-- Upper bound on the integrand: $(1 - \cos(tx)) K(x) \le 2\sqrt{|t|} (\sqrt{x} K(x))$ for $x > 0$. -/
theorem kernel_product_le_two_sqrt_mul (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (1 - Real.cos (t * x)) * K_kernel x ≤ 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x) := by
  have h_cos := one_sub_cos_mul_le_two_sqrt_mul t hx
  have h_K_nonneg := K_kernel_nonneg x hx
  calc (1 - Real.cos (t * x)) * K_kernel x
      ≤ (2 * Real.sqrt |t| * Real.sqrt x) * K_kernel x := mul_le_mul_of_nonneg_right h_cos h_K_nonneg
    _ = 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x) := by ring

/-- Main Upper Bound Theorem:
$$ \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) \le 2 C_K \sqrt{|t|} $$
for all $t \in \mathbb{R}$, provided the majorizing integral is integrable.
-/
theorem digamma_diff_le_two_C_K_sqrt (t : ℝ)
    (h_maj : IntegrableOn (fun x => 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x)) (Ioi 0)) :
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    (Complex.digamma ((1/4 : ℝ) : ℂ)).re ≤ 2 * C_K * Real.sqrt |t| := by
  rw [digamma_diff_eq_kernel_integral t]
  have h_int_lhs : IntegrableOn (fun x => (1 - Real.cos (t * x)) * K_kernel x) (Ioi 0) :=
    integrableOn_kernel_product t
  have h_ae_le : (fun x => (1 - Real.cos (t * x)) * K_kernel x) ≤ᵐ[volume.restrict (Ioi 0)]
                 (fun x => 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro x hx
    exact kernel_product_le_two_sqrt_mul t hx
  have h_mono := integral_mono_ae h_int_lhs h_maj h_ae_le
  have h_const : (∫ x in Ioi 0, 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x)) =
                 2 * Real.sqrt |t| * C_K := by
    unfold C_K
    exact integral_const_mul (2 * Real.sqrt |t|) (fun x => Real.sqrt x * K_kernel x)
  rw [h_const] at h_mono
  calc (∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x)
      ≤ 2 * Real.sqrt |t| * C_K := h_mono
    _ = 2 * C_K * Real.sqrt |t| := by ring

/-- **Main Sandwich Bound Theorem (Requirement X3 Main Result)**:
For any $t \in \mathbb{R}$,
$$ 0 \le \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) \le 2 C_K \sqrt{|t|} $$
-/
theorem digamma_diff_sandwich_sqrt (t : ℝ)
    (h_maj : IntegrableOn (fun x => 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x)) (Ioi 0)) :
    0 ≤ (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re ∧
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    (Complex.digamma ((1/4 : ℝ) : ℂ)).re ≤ 2 * C_K * Real.sqrt |t| :=
  ⟨digamma_diff_nonneg t, digamma_diff_le_two_C_K_sqrt t h_maj⟩

end RH_GammaSqrtBound


/-! ## Part 3: Square-Root Integrability & Unconditional Sandwich (Y1 Integration) -/

namespace RH_SqrtKernel

open RH_GammaSqrtBound

/-- Pointwise and global integrability of $\sqrt{x} K(x)$ on $(0, \infty)$. -/
theorem integrableOn_sqrt_kernel :
    IntegrableOn (fun x : ℝ => Real.sqrt x * K_kernel x) (Ioi 0) := by
  apply integrableOn_sqrt_envelope.mono'
  · exact (by unfold K_kernel; fun_prop : Measurable (fun x : ℝ => Real.sqrt x * K_kernel x)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro x hx
    rw [Real.norm_of_nonneg (sqrt_mul_K_kernel_nonneg x hx)]
    have h := mul_le_mul_of_nonneg_left (K_kernel_le_bound x hx) (Real.sqrt_nonneg x)
    have heq : Real.sqrt x * (Real.exp (-x / 2) * (2 + 1 / x)) =
        2 * (x ^ (1/2 : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ (1 : ℝ))) +
        x ^ (-1/2 : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ (1 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      rw [show (-1/2 : ℝ) = 1/2 - 1 by norm_num, Real.rpow_sub hx]
      simp only [Real.rpow_one]
      have he : -(1/2 : ℝ) * x = -x / 2 := by ring
      rw [he]
      ring
    rwa [heq] at h

/-- The majorant $x \mapsto 2 \sqrt{|t|} (\sqrt{x} K(x))$ is unconditionally integrable for all $t \in \mathbb{R}$. -/
theorem majorant_integrable (t : ℝ) :
    IntegrableOn (fun x : ℝ => 2 * Real.sqrt |t| * (Real.sqrt x * K_kernel x)) (Ioi 0) :=
  integrableOn_sqrt_kernel.const_mul (2 * Real.sqrt |t|)

/-- **Unconditional Sandwich Bound Theorem (Y1 Result)**:
For any $t \in \mathbb{R}$,
$$ 0 \le \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) \le 2 C_K \sqrt{|t|} $$
holding unconditionally without any majorant hypothesis `h_maj`. -/
theorem digamma_diff_sandwich_sqrt_unconditional (t : ℝ) :
    0 ≤ (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re ∧
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re ≤ 2 * C_K * Real.sqrt |t| :=
  digamma_diff_sandwich_sqrt t (majorant_integrable t)

end RH_SqrtKernel


/-! ## Part 4: General Weighted L1 Fubini Interchange (Y2 Implementation) -/

namespace RH_GammaWeightedFubini

open RH_GammaSqrtBound RH_SqrtKernel

/-- The two-variable Archimedean kernel integrand:
$$ H(a, t, x) = a(t) (1 - \cos(tx)) K(x) $$
-/
noncomputable def H_integrand (a : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p.1 * (1 - Real.cos (p.1 * p.2)) * K_kernel p.2

/-- Measurability of the two-variable integrand $H(a, t, x)$ on the product space $\mathbb{R} \times (0, \infty)$. -/
theorem H_aestronglyMeasurable (a : ℝ → ℝ) (ha_meas : Measurable a) :
    AEStronglyMeasurable (H_integrand a)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have h1 : Measurable (fun (p : ℝ × ℝ) => a p.1) := Measurable.comp ha_meas measurable_fst
  have h2 : Continuous (fun (p : ℝ × ℝ) => 1 - Real.cos (p.1 * p.2)) := by
    continuity
  have h3 : Measurable (fun (p : ℝ × ℝ) => K_kernel p.2) := by
    have hK : Measurable K_kernel := by unfold K_kernel; fun_prop
    exact Measurable.comp hK measurable_snd
  have h_prod : Measurable (fun (p : ℝ × ℝ) => H_integrand a p) := by
    unfold H_integrand
    exact (h1.mul h2.measurable).mul h3
  exact h_prod.aestronglyMeasurable

/-- Integrability of the separable dominating function $(t, x) \mapsto (2 |a(t)| \sqrt{|t|}) (\sqrt{x} K(x))$
on the product space $\mathbb{R} \times (0, \infty)$. -/
theorem dom_integrable (a : ℝ → ℝ)
    (ha_sqrt : Integrable (fun t : ℝ => |a t| * Real.sqrt |t|) volume) :
    Integrable (fun p : ℝ × ℝ => (2 * |a p.1| * Real.sqrt |p.1|) * (Real.sqrt p.2 * K_kernel p.2))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hf : Integrable (fun t : ℝ => 2 * |a t| * Real.sqrt |t|) volume := by
    have : (fun t : ℝ => 2 * |a t| * Real.sqrt |t|) = (fun t : ℝ => 2 * (|a t| * Real.sqrt |t|)) := by
      ext t; ring
    rw [this]
    exact ha_sqrt.const_mul 2
  have hg : Integrable (fun x : ℝ => Real.sqrt x * K_kernel x) (volume.restrict (Ioi 0)) :=
    integrableOn_sqrt_kernel
  exact Integrable.mul_prod hf hg

/-- **Product Absolute Integrability Theorem**:
For any measurable function $a : \mathbb{R} \to \mathbb{R}$ with $\int_{\mathbb{R}} |a(t)| \sqrt{|t|} dt < \infty$,
the two-variable Archimedean integrand $H(a, t, x) = a(t) (1 - \cos(tx)) K(x)$ is absolutely integrable
on $\mathbb{R} \times (0, \infty)$ with respect to $\operatorname{volume} \times (\operatorname{volume}\vert_{(0,\infty)})$. -/
theorem integrable_H_prod (a : ℝ → ℝ) (ha_meas : Measurable a)
    (ha_sqrt : Integrable (fun t : ℝ => |a t| * Real.sqrt |t|) volume) :
    Integrable (H_integrand a) (volume.prod (volume.restrict (Ioi 0))) := by
  apply (dom_integrable a ha_sqrt).mono' (H_aestronglyMeasurable a ha_meas)
  have h_prod_res : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
    have h_univ : (volume : Measure ℝ) = (volume : Measure ℝ).restrict (univ : Set ℝ) := Measure.restrict_univ.symm
    nth_rw 1 [h_univ]
    exact Measure.prod_restrict (univ : Set ℝ) (Ioi (0 : ℝ))
  rw [h_prod_res]
  have h_set_meas : MeasurableSet ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  refine ae_restrict_of_forall_mem h_set_meas ?_
  intro p hp
  have hx_pos : 0 < p.2 := hp.2
  have hK_ge : 0 ≤ K_kernel p.2 := K_kernel_nonneg p.2 hx_pos
  have h_cos_pos : 0 ≤ 1 - Real.cos (p.1 * p.2) := one_sub_cos_nonneg (p.1 * p.2)
  have h_cos_le : 1 - Real.cos (p.1 * p.2) ≤ 2 * Real.sqrt |p.1 * p.2| :=
    one_sub_cos_le_two_sqrt_abs (p.1 * p.2)
  rw [Real.norm_eq_abs]
  have habs_eq : |H_integrand a p| =
      |a p.1| * (1 - Real.cos (p.1 * p.2)) * K_kernel p.2 := by
    unfold H_integrand
    rw [abs_mul, abs_mul, abs_of_nonneg h_cos_pos, abs_of_nonneg hK_ge]
  rw [habs_eq]
  have h_sqrt_mul : Real.sqrt |p.1 * p.2| = Real.sqrt |p.1| * Real.sqrt p.2 := by
    rw [abs_mul, abs_of_pos hx_pos, Real.sqrt_mul (abs_nonneg _)]
  rw [h_sqrt_mul] at h_cos_le
  calc |a p.1| * (1 - Real.cos (p.1 * p.2)) * K_kernel p.2
      ≤ |a p.1| * (2 * (Real.sqrt |p.1| * Real.sqrt p.2)) * K_kernel p.2 := by
        gcongr
    _ = (2 * |a p.1| * Real.sqrt |p.1|) * (Real.sqrt p.2 * K_kernel p.2) := by ring

/-- Section identity 1: factoring $a(t)$ out of the $x$-integral. -/
theorem integral_H_x_eq (a : ℝ → ℝ) (t : ℝ) :
    (∫ x in Ioi 0, H_integrand a (t, x)) =
    a t * (∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x) := by
  have : (fun x => H_integrand a (t, x)) =
      (fun x => a t * ((1 - Real.cos (t * x)) * K_kernel x)) := by
    ext x; unfold H_integrand; ring
  rw [this, integral_const_mul]

/-- Section identity 2: factoring $K(x)$ out of the $t$-integral. -/
theorem integral_H_t_eq (a : ℝ → ℝ) (x : ℝ) :
    (∫ t, H_integrand a (t, x)) =
    K_kernel x * (∫ t, a t * (1 - Real.cos (t * x))) := by
  have : (fun t => H_integrand a (t, x)) =
      (fun t => (a t * (1 - Real.cos (t * x))) * K_kernel x) := by
    ext t; unfold H_integrand; ring
  rw [this, integral_mul_const, mul_comm]

/-- **Weighted Fubini Interchange Theorem for Archimedean Kernel**:
For any measurable $a : \mathbb{R} \to \mathbb{R}$ with $\int_{\mathbb{R}} |a(t)| \sqrt{|t|} dt < \infty$,
$$ \int_{\mathbb{R}} a(t) \left( \int_0^\infty (1 - \cos(tx)) K(x) \, dx \right) dt = \int_0^\infty K(x) \left( \int_{\mathbb{R}} a(t) (1 - \cos(tx)) \, dt \right) dx $$
-/
theorem weighted_fubini_kernel (a : ℝ → ℝ) (ha_meas : Measurable a)
    (ha_sqrt : Integrable (fun t : ℝ => |a t| * Real.sqrt |t|) volume) :
    (∫ t, a t * (∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x)) =
    (∫ x in Ioi 0, K_kernel x * (∫ t, a t * (1 - Real.cos (t * x)))) := by
  have h_int : Integrable (H_integrand a) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_H_prod a ha_meas ha_sqrt
  have h_swap : (∫ t, ∫ x in Ioi 0, H_integrand a (t, x)) =
      (∫ x in Ioi 0, ∫ t, H_integrand a (t, x)) :=
    integral_integral_swap h_int
  have h_lhs : (fun t => ∫ x in Ioi 0, H_integrand a (t, x)) =
      (fun t => a t * (∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x)) := by
    ext t; exact integral_H_x_eq a t
  have h_rhs : (fun x => ∫ t, H_integrand a (t, x)) =
      (fun x => K_kernel x * (∫ t, a t * (1 - Real.cos (t * x)))) := by
    ext x; exact integral_H_t_eq a x
  rw [h_lhs, h_rhs] at h_swap
  exact h_swap

/-- **Weighted Fubini Interchange with Digamma Difference Representation (Main Y2 Theorem)**:
For any measurable $a : \mathbb{R} \to \mathbb{R}$ with $\int_{\mathbb{R}} |a(t)| \sqrt{|t|} dt < \infty$,
$$ \int_{\mathbb{R}} a(t) \left( \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) \right) dt = \int_0^\infty K(x) \left( \int_{\mathbb{R}} a(t) (1 - \cos(tx)) \, dt \right) dx $$
-/
theorem weighted_fubini_digamma (a : ℝ → ℝ) (ha_meas : Measurable a)
    (ha_sqrt : Integrable (fun t : ℝ => |a t| * Real.sqrt |t|) volume) :
    (∫ t, a t * ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
                 (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) =
    (∫ x in Ioi 0, K_kernel x * (∫ t, a t * (1 - Real.cos (t * x)))) := by
  have h_eq : (fun t => a t * ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
                               (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) =
              (fun t => a t * (∫ x in Ioi 0, (1 - Real.cos (t * x)) * K_kernel x)) := by
    ext t
    rw [← digamma_diff_eq_kernel_integral t]
  rw [h_eq]
  exact weighted_fubini_kernel a ha_meas ha_sqrt

end RH_GammaWeightedFubini

namespace RH_GammaFourierBridge

open RH_GammaSqrtBound RH_SqrtKernel RH_GammaWeightedFubini
open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate

/-! ## Part 7: Fourier Decay and (Weighted) L1 Integrability for C² Compactly Supported Functions (Z1) -/

-- Helper: Integrable from 3 intervals
lemma integrable_of_three_intervals {g : ℝ → ℝ}
    (h1 : IntegrableOn g (Iic (-1)))
    (h2 : IntegrableOn g (Icc (-1) 1))
    (h3 : IntegrableOn g (Ioi 1)) :
    Integrable g := by
  have h12 : IntegrableOn g (Iic 1) := by
    have : (Iic 1 : Set ℝ) = Iic (-1) ∪ Icc (-1) 1 := by
      ext x; simp only [mem_Iic, mem_union, mem_Icc]
      constructor
      · intro hx
        by_cases h : x ≤ -1
        · exact Or.inl h
        · have : -1 < x := not_le.mp h
          exact Or.inr ⟨this.le, hx⟩
      · rintro (h | ⟨h, h'⟩)
        · exact h.trans (by norm_num)
        · exact h'
    rw [this]
    exact h1.union h2
  have h_univ : (univ : Set ℝ) = Iic 1 ∪ Ioi 1 := by
    ext x; simp only [mem_univ, true_iff, mem_union, mem_Iic, mem_Ioi]
    exact le_or_gt x 1
  have h_all : IntegrableOn g univ := by
    rw [h_univ]
    exact h12.union h3
  exact integrableOn_univ.mp h_all

/-- Fourier transform norm L1 integrability for C² compactly supported functions. -/
theorem integrable_norm_paperFT (f : ℝ → ℂ) {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun t : ℝ => ‖paperFT f (t : ℂ)‖) := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  set C₀ : ℝ := ∫ u, ‖f u‖
  set C₂ : ℝ := ∫ u, ‖deriv (deriv f) u‖
  set K : ℝ := C₀ + C₂
  have hG : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ ≤ C₀ := by
    intro r
    simpa using Zeta23.norm_paperFT_le hfi hsupp (r : ℂ)
  have hG2 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * r ^ 2 ≤ C₂ := by
    intro r
    have := Zeta23.norm_paperFT_mul_sq_le hf hsupp (r : ℂ)
    simpa [sq_abs] using this
  have hGK : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * (1 + r ^ 2) ≤ K := by
    intro r
    have := hG r; have := hG2 r
    simp only [K]; nlinarith
  have hcont : Continuous fun (r : ℝ) => ‖paperFT f (r : ℂ)‖ :=
    (Zeta23.Taper.contDiff_paperFT_ofReal hf.continuous hcs 0).continuous.norm
  apply Zeta23.Taper.integrable_of_abs_mul_one_add_sq_le hcont (K := K)
  intro r
  rw [abs_of_nonneg (norm_nonneg _)]
  exact hGK r

/-- Fourier transform real part L1 integrability for C² compactly supported functions. -/
theorem integrable_re_paperFT (f : ℝ → ℂ) {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun t : ℝ => (paperFT f (t : ℂ)).re) := by
  have h_norm := integrable_norm_paperFT f hf hsupp
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hcont : Continuous fun (t : ℝ) => (paperFT f (t : ℂ)).re :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal hf.continuous hcs 0).continuous
  refine h_norm.mono' hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (paperFT f (t : ℂ))

/-- Weighted Fourier transform norm integrability: t ↦ ‖paperFT f t‖ * √|t| is integrable. -/
theorem integrable_norm_paperFT_mul_sqrt (f : ℝ → ℂ) {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun t : ℝ => ‖paperFT f (t : ℂ)‖ * Real.sqrt |t|) := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hcont_FT : Continuous fun (r : ℝ) => paperFT f (r : ℂ) :=
    Zeta23.Taper.contDiff_paperFT_ofReal hf.continuous hcs 0 |>.continuous
  have hcont_g : Continuous fun (t : ℝ) => ‖paperFT f (t : ℂ)‖ * Real.sqrt |t| := by
    have hc1 : Continuous fun (t : ℝ) => ‖paperFT f (t : ℂ)‖ := hcont_FT.norm
    have hc2 : Continuous fun (t : ℝ) => Real.sqrt |t| := continuous_sqrt.comp continuous_abs
    exact hc1.mul hc2
  set C₂ : ℝ := ∫ u, ‖deriv (deriv f) u‖
  have hC₂_nonneg : 0 ≤ C₂ := integral_nonneg fun _ => norm_nonneg _
  have hG2 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * r ^ 2 ≤ C₂ := by
    intro r
    have := Zeta23.norm_paperFT_mul_sq_le hf hsupp (r : ℂ)
    simpa [sq_abs] using this

  -- Interval 2: Icc (-1) 1
  have h2 : IntegrableOn (fun t : ℝ => ‖paperFT f (t : ℂ)‖ * Real.sqrt |t|) (Icc (-1) 1) :=
    hcont_g.continuousOn.integrableOn_compact isCompact_Icc

  -- Interval 3: Ioi 1
  have h_rpow : IntegrableOn (fun t : ℝ => t ^ (-3/2 : ℝ)) (Ioi 1) := by
    have hs : (-3/2 : ℝ) < -1 := by norm_num
    exact integrableOn_Ioi_rpow_of_lt hs zero_lt_one
  have h_maj3 : IntegrableOn (fun t : ℝ => C₂ * t ^ (-3/2 : ℝ)) (Ioi 1) :=
    h_rpow.const_mul C₂
  have h3 : IntegrableOn (fun t : ℝ => ‖paperFT f (t : ℂ)‖ * Real.sqrt |t|) (Ioi 1) := by
    refine h_maj3.mono' (hcont_g.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have h_nonneg : 0 ≤ ‖paperFT f (t : ℂ)‖ * Real.sqrt |t| := by positivity
    rw [Real.norm_of_nonneg h_nonneg]
    rw [abs_of_pos ht0]
    have ht2_pos : 0 < t ^ 2 := by positivity
    have h_div : ‖paperFT f (t : ℂ)‖ ≤ C₂ / t ^ 2 := by
      have := hG2 t
      rwa [le_div_iff₀ ht2_pos]
    have h_pow_step : (C₂ / t ^ 2) * Real.sqrt t = C₂ * (t ^ (-2 : ℝ) * t ^ (1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      have h_pow : t ^ (-2 : ℝ) = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0.le 2
      rw [h_pow, Real.rpow_two, div_eq_mul_inv]
      ring
    have h_add : t ^ (-2 : ℝ) * t ^ (1/2 : ℝ) = t ^ (-3/2 : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      norm_num
    calc ‖paperFT f (t : ℂ)‖ * Real.sqrt t
        ≤ (C₂ / t ^ 2) * Real.sqrt t := mul_le_mul_of_nonneg_right h_div (Real.sqrt_nonneg t)
      _ = C₂ * (t ^ (-2 : ℝ) * t ^ (1/2 : ℝ)) := h_pow_step
      _ = C₂ * t ^ (-3/2 : ℝ) := by rw [h_add]

  -- Interval 1: Iic (-1) via reflection
  have h1 : IntegrableOn (fun t : ℝ => ‖paperFT f (t : ℂ)‖ * Real.sqrt |t|) (Iic (-1)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_neg]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hcont_comp : Continuous fun (x : ℝ) => ‖paperFT f ((-x : ℝ) : ℂ)‖ * Real.sqrt |-x| := by
      have hc1 : Continuous fun (x : ℝ) => paperFT f ((-x : ℝ) : ℂ) :=
        hcont_FT.comp continuous_neg
      have hc2 : Continuous fun (x : ℝ) => Real.sqrt |-x| :=
        continuous_sqrt.comp (continuous_abs.comp continuous_neg)
      exact hc1.norm.mul hc2
    refine h_maj3.mono' (hcont_comp.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have h_nonneg : 0 ≤ ‖paperFT f ((-t : ℝ) : ℂ)‖ * Real.sqrt |-t| := by positivity
    rw [Real.norm_of_nonneg h_nonneg]
    rw [abs_neg, abs_of_pos ht0]
    have hG2_neg : ‖paperFT f ((-t : ℝ) : ℂ)‖ * t ^ 2 ≤ C₂ := by
      simpa [sq_abs] using Zeta23.norm_paperFT_mul_sq_le hf hsupp ((-t : ℝ) : ℂ)
    have ht2_pos : 0 < t ^ 2 := by positivity
    have h_div : ‖paperFT f ((-t : ℝ) : ℂ)‖ ≤ C₂ / t ^ 2 := by
      rwa [le_div_iff₀ ht2_pos]
    have h_pow_step : (C₂ / t ^ 2) * Real.sqrt t = C₂ * (t ^ (-2 : ℝ) * t ^ (1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      have h_pow : t ^ (-2 : ℝ) = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0.le 2
      rw [h_pow, Real.rpow_two, div_eq_mul_inv]
      ring
    have h_add : t ^ (-2 : ℝ) * t ^ (1/2 : ℝ) = t ^ (-3/2 : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      norm_num
    calc ‖paperFT f ((-t : ℝ) : ℂ)‖ * Real.sqrt t
        ≤ (C₂ / t ^ 2) * Real.sqrt t := mul_le_mul_of_nonneg_right h_div (Real.sqrt_nonneg t)
      _ = C₂ * (t ^ (-2 : ℝ) * t ^ (1/2 : ℝ)) := h_pow_step
      _ = C₂ * t ^ (-3/2 : ℝ) := by rw [h_add]

  exact integrable_of_three_intervals h1 h2 h3

/-- Weighted Fourier transform real part integrability: t ↦ |Re(paperFT f t)| * √|t| is integrable. -/
theorem integrable_re_paperFT_mul_sqrt (f : ℝ → ℂ) {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun t : ℝ => |(paperFT f (t : ℂ)).re| * Real.sqrt |t|) := by
  have h_norm := integrable_norm_paperFT_mul_sqrt f hf hsupp
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hcont_re : Continuous fun (t : ℝ) => (paperFT f (t : ℂ)).re :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal hf.continuous hcs 0).continuous
  have hcont_w : Continuous fun (t : ℝ) => |(paperFT f (t : ℂ)).re| * Real.sqrt |t| :=
    hcont_re.abs.mul (continuous_sqrt.comp continuous_abs)
  refine h_norm.mono' hcont_w.aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  have h_nonneg : 0 ≤ |(paperFT f (t : ℂ)).re| * Real.sqrt |t| := by positivity
  rw [Real.norm_of_nonneg h_nonneg]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Complex.abs_re_le_norm (paperFT f (t : ℂ))

/-! ## Part 8: Cosine Inversion and Specialized Main Connection for Real Even Functions (Z2) -/

/-- For real even C² compactly supported h, the cosine transform satisfies:
$$ \int_{\mathbb{R}} a(t) \cos(tx) dt = 2\pi h(x) $$
where $a(t) = \operatorname{Re}(\operatorname{paperFT} h (t))$. -/
theorem integral_mul_cos_even_h (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (heven : ∀ u, h (-u) = h u) (x : ℝ) :
    ∫ (t : ℝ), (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * Real.cos (t * x) = 2 * π * h x := by
  have h_int_h : Integrable h := hf.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hsupp)
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have h_int_a : Integrable (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    integrable_re_paperFT (fun u => (h u : ℂ)) hf_c hsupp_c
  have hFT : ∀ r : ℝ, paperFT (fun u => (h u : ℂ)) (r : ℂ) =
      (((paperFT (fun u => (h u : ℂ)) (r : ℂ)).re : ℝ) : ℂ) := by
    intro r
    exact Zeta23.Taper.paperFT_ofReal_eq_re heven r
  exact Zeta23.Taper.integral_mul_cos_of_paperFT_eq hf.continuous h_int_h h_int_a hFT x

/-- Value at x = 0:
$$ \int_{\mathbb{R}} a(t) dt = 2\pi h(0) $$ -/
theorem integral_even_h_at_zero (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (heven : ∀ u, h (-u) = h u) :
    ∫ (t : ℝ), (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re = 2 * π * h 0 := by
  have := integral_mul_cos_even_h h hf hsupp heven 0
  simpa only [mul_zero, Real.cos_zero, mul_one] using this

/-- Integrability of `a(t) * cos(t * x)` -/
theorem integrable_a_mul_cos (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (x : ℝ) :
    Integrable (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * Real.cos (t * x)) := by
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have h_norm := integrable_norm_paperFT (fun u => (h u : ℂ)) hf_c hsupp_c
  have hcs : HasCompactSupport (fun u => (h u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupp_c
  have hcont_a : Continuous fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal (Complex.continuous_ofReal.comp hf.continuous) hcs 0).continuous
  have hcont_prod : Continuous fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * Real.cos (t * x) :=
    hcont_a.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  refine h_norm.mono' hcont_prod.aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(paperFT (fun u => (h u : ℂ)) (t : ℂ)).re| ≤ ‖paperFT (fun u => (h u : ℂ)) (t : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : |Real.cos (t * x)| ≤ 1 := Real.abs_cos_le_one (t * x)
  calc |(paperFT (fun u => (h u : ℂ)) (t : ℂ)).re| * |Real.cos (t * x)|
      ≤ ‖paperFT (fun u => (h u : ℂ)) (t : ℂ)‖ * 1 := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = ‖paperFT (fun u => (h u : ℂ)) (t : ℂ)‖ := mul_one _

/-- Cosine difference inversion identity:
$$ \int_{\mathbb{R}} a(t) (1 - \cos(tx)) dt = 2\pi (h(0) - h(x)) $$ -/
theorem integral_a_mul_one_sub_cos (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (heven : ∀ u, h (-u) = h u) (x : ℝ) :
    ∫ (t : ℝ), (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * (1 - Real.cos (t * x)) =
    2 * π * (h 0 - h x) := by
  have h_eq : (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * (1 - Real.cos (t * x))) =
      (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re -
                      (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * Real.cos (t * x)) := by
    funext t; ring
  rw [h_eq]
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have h_int_a : Integrable (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    integrable_re_paperFT (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_int_cos : Integrable (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re * Real.cos (t * x)) :=
    integrable_a_mul_cos h hf hsupp x
  rw [integral_sub h_int_a h_int_cos]
  rw [integral_even_h_at_zero h hf hsupp heven]
  rw [integral_mul_cos_even_h h hf hsupp heven x]
  ring

/-- **Main Connection Theorem (Z2)**:
For any real even $C^2$ function $h$ with compact support,
$$ \int_{\mathbb{R}} a(t) \left( \operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4) \right) dt = 2\pi \int_0^\infty K(x) (h(0) - h(x)) \, dx $$ -/
theorem weighted_fubini_even_h (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (heven : ∀ u, h (-u) = h u) :
    (∫ (t : ℝ), (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
       ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) =
    2 * π * ∫ x in Ioi 0, K_kernel x * (h 0 - h x) := by
  set a : ℝ → ℝ := fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have hcs : HasCompactSupport (fun u => (h u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupp_c
  have ha_cont : Continuous a :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal (Complex.continuous_ofReal.comp hf.continuous) hcs 0).continuous
  have ha_meas : Measurable a := ha_cont.measurable
  have ha_sqrt : Integrable (fun t => |a t| * Real.sqrt |t|) volume :=
    integrable_re_paperFT_mul_sqrt (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_fub := weighted_fubini_digamma a ha_meas ha_sqrt
  rw [h_fub]
  have h_inner : (fun x => K_kernel x * (∫ (t : ℝ), a t * (1 - Real.cos (t * x)))) =
      (fun x => (2 * π) * (K_kernel x * (h 0 - h x))) := by
    ext x
    rw [integral_a_mul_one_sub_cos h hf hsupp heven x]
    ring
  rw [h_inner]
  rw [integral_const_mul]

/-! ## Part 9: Explicit Integrability of Both Sides (Z3) -/

/-- Integrability of the LHS Digamma Integrand:
$t \mapsto a(t) (\operatorname{Re}\psi(1/4 + it/2) - \operatorname{Re}\psi(1/4))$ is integrable on $\mathbb{R}$. -/
theorem integrable_lhs_digamma (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
       ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) := by
  set a : ℝ → ℝ := fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have hcs : HasCompactSupport (fun u => (h u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupp_c
  have ha_cont : Continuous a :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal (Complex.continuous_ofReal.comp hf.continuous) hcs 0).continuous
  have ha_meas : Measurable a := ha_cont.measurable
  have ha_sqrt : Integrable (fun t => |a t| * Real.sqrt |t|) volume :=
    integrable_re_paperFT_mul_sqrt (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_int : Integrable (H_integrand a) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_H_prod a ha_meas ha_sqrt
  have h_left := h_int.integral_prod_left
  have h_eq : (fun (t : ℝ) => ∫ x in Ioi 0, H_integrand a (t, x)) =
      (fun (t : ℝ) => a t * ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
                             (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) := by
    ext t
    rw [integral_H_x_eq]
    rw [← digamma_diff_eq_kernel_integral t]
  rwa [h_eq] at h_left

/-- Integrability of the RHS Kernel Integrand:
$x \mapsto K(x) (h(0) - h(x))$ is integrable on $(0, \infty)$. -/
theorem integrable_rhs_kernel (h : ℝ → ℝ) {Λ : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (heven : ∀ u, h (-u) = h u) :
    IntegrableOn (fun x : ℝ => K_kernel x * (h 0 - h x)) (Ioi 0) := by
  set a : ℝ → ℝ := fun (t : ℝ) => (paperFT (fun u => (h u : ℂ)) (t : ℂ)).re
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have hcs : HasCompactSupport (fun u => (h u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupp_c
  have ha_cont : Continuous a :=
    (Zeta23.Taper.contDiff_re_paperFT_ofReal (Complex.continuous_ofReal.comp hf.continuous) hcs 0).continuous
  have ha_meas : Measurable a := ha_cont.measurable
  have ha_sqrt : Integrable (fun t => |a t| * Real.sqrt |t|) volume :=
    integrable_re_paperFT_mul_sqrt (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_int : Integrable (H_integrand a) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_H_prod a ha_meas ha_sqrt
  have h_right := h_int.integral_prod_right
  have h_eq : (fun (x : ℝ) => ∫ (t : ℝ), H_integrand a (t, x)) =
      (fun x => (2 * π) * (K_kernel x * (h 0 - h x))) := by
    ext x
    rw [integral_H_t_eq]
    rw [integral_a_mul_one_sub_cos h hf hsupp heven x]
    ring
  rw [h_eq] at h_right
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have h_cancel : (fun x : ℝ => K_kernel x * (h 0 - h x)) =
      (fun x => (2 * π)⁻¹ * ((2 * π) * (K_kernel x * (h 0 - h x)))) := by
    ext x
    rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
  rw [h_cancel]
  exact h_right.const_mul (2 * π)⁻¹

end RH_GammaFourierBridge



/-! ==========================================================================
  PART C: Integration with Constant and Tail (Task 0072 / GammaFinalFormula)
  ========================================================================== -/

namespace RH_GammaFinalFormula

open Real MeasureTheory Set Filter
open scoped Topology Interval

/-- Digamma value at 1/4 -/
noncomputable def psi_0 : ℝ := (Complex.digamma ((1/4 : ℝ) : ℂ)).re

/-- Constant log pi -/
noncomputable def log_pi : ℝ := Real.log Real.pi

/-- The Archimedean Gamma tail function T(b) -/
noncomputable def T_tail (b : ℝ) : ℝ := RH_Rebaseline.T_tail b

/-- The kernel K(x) -/
noncomputable def K_kernel (x : ℝ) : ℝ := RH_GammaSqrtBound.K_kernel x

/-- The Fourier transform real part of h -/
noncomputable def a_func (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re

/-- Kernel equivalence between RH_GammaSqrtBound and RH_Rebaseline -/
theorem K_kernel_eq_Rebaseline :
    K_kernel = RH_Rebaseline.K_kernel := rfl

/-- Complete Gamma functional G(h) with constant term log pi -/
noncomputable def G_functional (h : ℝ → ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t : ℝ, a_func h t *
    ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - log_pi)

/-- Finite-interval Gamma functional A_b(h) -/
noncomputable def A_b (h : ℝ → ℝ) (b : ℝ) : ℝ :=
  (log_pi - psi_0 - T_tail b) * h 0 +
    ∫ x in Ioc 0 b, (h x - h 0) * K_kernel x

/-! ### E1: Integrability and Formula with Constant -/

/-- Integrability of the full Gamma integrand with constant log pi (E1) -/
theorem integrable_a_mul_digamma_sub_log_pi (h : ℝ → ℝ) {b : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) :
    Integrable (fun (t : ℝ) => a_func h t *
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - log_pi)) := by
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ b := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have h_digamma : Integrable (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
      (((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re))) :=
    RH_GammaFourierBridge.integrable_lhs_digamma h hf hsupp
  have h_a_l1 : Integrable (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    RH_GammaFourierBridge.integrable_re_paperFT (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_const_mul : Integrable (fun (t : ℝ) => (psi_0 - log_pi) * (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    h_a_l1.const_mul (psi_0 - log_pi)
  have h_sum := h_digamma.add h_const_mul
  have h_eq : (fun (t : ℝ) => a_func h t *
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - log_pi)) =
      (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
        (((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) +
        (psi_0 - log_pi) * (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) := by
    ext t
    dsimp [a_func, psi_0, log_pi]
    ring
  rwa [h_eq]

/-- Main Gamma formula with constant log pi (E1) -/
theorem gamma_integral_with_const (h : ℝ → ℝ) {b : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    G_functional h = (psi_0 - log_pi) * h 0 + ∫ x in Ioi 0, K_kernel x * (h 0 - h x) := by
  dsimp [G_functional]
  have hf_c : ContDiff ℝ 2 (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsupp_c : ∀ u, (h u : ℂ) ≠ 0 → |u| ≤ b := by
    intro u hu
    have : h u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hsupp u this
  have h_digamma : Integrable (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
      (((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma ((1/4 : ℝ) : ℂ)).re))) :=
    RH_GammaFourierBridge.integrable_lhs_digamma h hf hsupp
  have h_a_l1 : Integrable (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    RH_GammaFourierBridge.integrable_re_paperFT (fun u => (h u : ℂ)) hf_c hsupp_c
  have h_const_mul : Integrable (fun (t : ℝ) => (psi_0 - log_pi) * (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) :=
    h_a_l1.const_mul (psi_0 - log_pi)
  have h_split : (∫ t : ℝ, a_func h t *
      ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - log_pi)) =
      (∫ t : ℝ, (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
        (((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          (Complex.digamma ((1/4 : ℝ) : ℂ)).re))) +
      ∫ t : ℝ, (psi_0 - log_pi) * (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re := by
    have h_eq : (fun (t : ℝ) => a_func h t *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re - log_pi)) =
        (fun (t : ℝ) => (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re *
          (((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            (Complex.digamma ((1/4 : ℝ) : ℂ)).re)) +
          (psi_0 - log_pi) * (Zeta23.paperFT (fun u => (h u : ℂ)) (t : ℂ)).re) := by
      ext t; dsimp [a_func, psi_0, log_pi]; ring
    rw [h_eq]
    exact integral_add h_digamma h_const_mul
  rw [h_split]
  have h_fub := RH_GammaFourierBridge.weighted_fubini_even_h h hf hsupp heven
  rw [h_fub]
  rw [integral_const_mul]
  have h_zero := RH_GammaFourierBridge.integral_even_h_at_zero h hf hsupp heven
  rw [h_zero]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have h_cancel : (2 * π)⁻¹ * (2 * π) = (1 : ℝ) := inv_mul_cancel₀ h2pi
  set I_val := ∫ (x : ℝ) in Ioi 0, RH_GammaSqrtBound.K_kernel x * (h 0 - h x)
  change (2 * π)⁻¹ * ((2 * π * I_val) + (psi_0 - log_pi) * (2 * π * h 0)) = (psi_0 - log_pi) * h 0 + I_val
  calc
    (2 * π)⁻¹ * ((2 * π * I_val) + (psi_0 - log_pi) * (2 * π * h 0))
      = ((2 * π)⁻¹ * (2 * π)) * I_val + ((2 * π)⁻¹ * (2 * π)) * ((psi_0 - log_pi) * h 0) := by ring
    _ = 1 * I_val + 1 * ((psi_0 - log_pi) * h 0) := by rw [h_cancel]
    _ = (psi_0 - log_pi) * h 0 + I_val := by ring

/-! ### E2: Splitting Integral and Connecting to Analytic Tail T(b) -/

/-- Integrability of kernel on (0, b] (E2) -/
theorem integrableOn_Ioc_kernel_sub (h : ℝ → ℝ) {b : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    IntegrableOn (fun x : ℝ => K_kernel x * (h 0 - h x)) (Ioc 0 b) := by
  have h_int := RH_GammaFourierBridge.integrable_rhs_kernel h hf hsupp heven
  exact h_int.mono_set (fun x hx => hx.1)

/-- Integrability of kernel on (b, ∞) (E2) -/
theorem integrableOn_Ioi_kernel_sub (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b) (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    IntegrableOn (fun x : ℝ => K_kernel x * (h 0 - h x)) (Ioi b) := by
  have h_int := RH_GammaFourierBridge.integrable_rhs_kernel h hf hsupp heven
  exact h_int.mono_set (fun x hx => lt_trans hb hx)

/-- Integral on the tail (b, ∞) equals h(0) * T(b) (E2) -/
theorem integral_Ioi_tail_kernel_sub (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) :
    (∫ x in Ioi b, K_kernel x * (h 0 - h x)) = h 0 * T_tail b := by
  have h_eq : ∀ x ∈ Ioi b, K_kernel x * (h 0 - h x) = h 0 * K_kernel x := by
    intro x hx
    have hx_gt : b < x := hx
    have hx_abs : b < |x| := by
      have : 0 < x := lt_trans hb hx_gt
      rw [abs_of_pos this]
      exact hx_gt
    have h_zero : h x = 0 := by
      by_contra hc
      have h_le := hsupp x hc
      linarith
    rw [h_zero, sub_zero, mul_comm]
  have h_set_eq : (∫ x in Ioi b, K_kernel x * (h 0 - h x)) = ∫ x in Ioi b, h 0 * K_kernel x :=
    setIntegral_congr_fun (μ := volume) measurableSet_Ioi h_eq
  rw [h_set_eq]
  rw [integral_const_mul]
  have h_tail := RH_Rebaseline.integral_Ioi_K_kernel_eq_T_tail hb
  dsimp [T_tail, K_kernel]
  have h_k : (fun x => RH_GammaSqrtBound.K_kernel x) = RH_Rebaseline.K_kernel := rfl
  rw [h_k, h_tail]

/-- Splitting theorem between finite interval (0, b] and analytical tail T(b) (E2) -/
theorem integral_kernel_split_tail (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b) (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    (∫ x in Ioi 0, K_kernel x * (h 0 - h x)) =
    (∫ x in Ioc 0 b, K_kernel x * (h 0 - h x)) + h 0 * T_tail b := by
  have h_disj : Disjoint (Ioc 0 b) (Ioi b) := Ioc_disjoint_Ioi (le_refl b)
  have h_union : Ioc 0 b ∪ Ioi b = Ioi 0 := Ioc_union_Ioi_eq_Ioi (le_of_lt hb)
  have h_ioc := integrableOn_Ioc_kernel_sub h hf hsupp heven
  have h_ioi := integrableOn_Ioi_kernel_sub h hb hf hsupp heven
  have h_split := setIntegral_union h_disj measurableSet_Ioi h_ioc h_ioi
  rw [h_union] at h_split
  rw [h_split]
  rw [integral_Ioi_tail_kernel_sub h hb hsupp]

/-! ### E3: Final Formula G(h) = - A_b(h) -/

/-- Final Gamma formula: G(h) = - A_b(h) (E3) -/
theorem gamma_eq_neg_A_b (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b) (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    G_functional h = - A_b h b := by
  have h_e1 := gamma_integral_with_const h hf hsupp heven
  have h_e2 := integral_kernel_split_tail h hb hf hsupp heven
  rw [h_e1, h_e2]
  dsimp [A_b]
  set I_ioc := ∫ x in Ioc 0 b, (h x - h 0) * K_kernel x
  have h_neg_int : (∫ x in Ioc 0 b, K_kernel x * (h 0 - h x)) = - I_ioc := by
    dsimp [I_ioc]
    rw [← integral_neg]
    have h_eq : (fun x => - ((h x - h 0) * K_kernel x)) = (fun x => K_kernel x * (h 0 - h x)) := by
      ext x; ring
    rw [h_eq]
  rw [h_neg_int]
  ring

end RH_GammaFinalFormula


/-! ==========================================================================
  PART D: Literature Explicit Formula and Full Real-Space Bridge (Task 0075)
  ========================================================================== -/

namespace RH_LiteratureBridge

open Real MeasureTheory Set Filter
open scoped Topology Interval ComplexConjugate FourierTransform

/-- Frequency-space Gamma integral from the literature explicit formula of Zeta23 -/
noncomputable def G_freq (h : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, Zeta23.paperFT h r * (Zeta23.EF.gammaBracket r : ℂ)

/-- Real-space pole term for an even test function h on [0, b] -/
noncomputable def P_pole (b : ℝ) (h : ℝ → ℝ) : ℝ :=
  4 * ∫ x in (0 : ℝ)..b, h x * Real.cosh (x / 2)

/-- Real-space prime power term -/
noncomputable def S_prime (h : ℝ → ℝ) : ℝ :=
  2 * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * h (Real.log n)

/-- Real-space Archimedean term (interval integral) -/
noncomputable def A_arch (b : ℝ) (h : ℝ → ℝ) : ℝ :=
  (Real.log Real.pi - (Complex.digamma (1 / 4 : ℂ)).re - RH_GammaFinalFormula.T_tail b) * h 0 +
  ∫ x in (0 : ℝ)..b, (h x - h 0) * RH_GammaFinalFormula.K_kernel x

/-- Real-space explicit formula quantity: W_real = P - S - A -/
noncomputable def W_real (b : ℝ) (h : ℝ → ℝ) : ℝ :=
  P_pole b h - S_prime h - A_arch b h

/-- For an even function h, the two-sided log evaluation reduces to 2 * h(log n). -/
theorem prime_summand_even {h : ℝ → ℝ} (heven : ∀ x, h (-x) = h x) (n : ℕ) :
    h (Real.log n) + h (-Real.log n) = 2 * h (Real.log n) := by
  rw [heven (Real.log n)]
  ring

/-- Transfer bounded support condition to topological support subset of Icc (-b) b -/
theorem tsupport_subset_Icc_of_supp_abs_le {h : ℝ → ℝ} {b : ℝ}
    (hsupp : ∀ x, h x ≠ 0 → |x| ≤ b) :
    tsupport (fun x => (h x : ℂ)) ⊆ Set.Icc (-b) b := by
  have h_supp : Function.support (fun x => (h x : ℂ)) ⊆ Set.Icc (-b) b := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have h_re : h x ≠ 0 := by
      intro h0; apply hx; simp [h0]
    have h_le : |x| ≤ b := hsupp x h_re
    rw [abs_le] at h_le
    exact ⟨h_le.1, h_le.2⟩
  exact closure_minimal h_supp isClosed_Icc

/-- Connection of the prime power sum to the real sum -/
theorem prime_term_bridge {h : ℝ → ℝ} {b : ℝ} (_hb : 0 < b)
    (heven : ∀ x, h (-x) = h x)
    (hsupp : tsupport (fun x => (h x : ℂ)) ⊆ Set.Icc (-b) b) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (((h (Real.log n) : ℝ) : ℂ) + ((h (-Real.log n) : ℝ) : ℂ))).re =
    2 * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * h (Real.log n) := by
  set S := Finset.Ioc 0 ⌊Real.exp b⌋₊
  have h_comp_zero : ∀ n ∉ S, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (((h (Real.log n) : ℝ) : ℂ) + ((h (-Real.log n) : ℝ) : ℂ)) = 0 := by
    intro n hn
    exact Zeta23.EF.prime_summand_eq_zero hsupp hn
  have h_real_zero : ∀ n ∉ S, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * h (Real.log n) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
    · have hn' : ⌊Real.exp b⌋₊ < n := by
        by_contra hle
        have : n ∈ S := Finset.mem_Ioc.mpr ⟨hpos, not_lt.mp hle⟩
        exact hn this
      have hX : Real.exp b < n := (Nat.floor_lt (Real.exp_pos b).le).mp hn'
      have hlog : b < Real.log n := by
        rw [← Real.log_exp b]
        exact Real.log_lt_log (Real.exp_pos b) hX
      have h1 : (fun x => (h x : ℂ)) (Real.log n) = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun x => (h x : ℂ))
        intro hmem
        exact (not_le.mpr hlog) (hsupp hmem).2
      have h1_re : h (Real.log n) = 0 := by
        exact_mod_cast congr_arg Complex.re h1
      rw [h1_re, mul_zero]
  rw [tsum_eq_sum (s := S) h_comp_zero]
  rw [tsum_eq_sum (s := S) h_real_zero]
  rw [← Complex.reCLM_apply, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.reCLM_apply]
  have h_add : (((h (Real.log n) : ℝ) : ℂ) + ((h (-Real.log n) : ℝ) : ℂ)) =
      ((2 * h (Real.log n) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    exact congr_arg Complex.ofReal (prime_summand_even heven n)
  have h_term : (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      ((2 * h (Real.log n) : ℝ) : ℂ)).re =
      2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * h (Real.log n)) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [h_add, h_term]

/-- Connection of the pole Fourier evaluation to the interval integral -/
theorem pole_term_bridge {h : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hcont : Continuous h)
    (heven : ∀ x, h (-x) = h x)
    (hsupp : tsupport (fun x => (h x : ℂ)) ⊆ Set.Icc (-b) b) :
    (Zeta23.paperFT (fun x => (h x : ℂ)) (Complex.I / 2) +
     Zeta23.paperFT (fun x => (h x : ℂ)) (-Complex.I / 2)).re =
    P_pole b h := by
  have hkc : HasCompactSupport (fun x => (h x : ℂ)) :=
    Zeta23.EF.hasCompactSupport_of_tsupport_subset hsupp
  have hcontC : Continuous (fun x => (h x : ℂ)) :=
    Complex.continuous_ofReal.comp hcont
  have h_cont_exp1 : Continuous (fun u : ℝ => Complex.exp (Complex.I * (Complex.I / 2) * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have h_cont_exp2 : Continuous (fun u : ℝ => Complex.exp (Complex.I * (-Complex.I / 2) * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hI1 : MeasureTheory.Integrable (fun u : ℝ => (h u : ℂ) * Complex.exp (Complex.I * (Complex.I / 2) * (u : ℂ))) :=
    (hcontC.mul h_cont_exp1).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : MeasureTheory.Integrable (fun u : ℝ => (h u : ℂ) * Complex.exp (Complex.I * (-Complex.I / 2) * (u : ℂ))) :=
    (hcontC.mul h_cont_exp2).integrable_of_hasCompactSupport hkc.mul_right
  have step1 : Zeta23.paperFT (fun x => (h x : ℂ)) (Complex.I / 2) +
      Zeta23.paperFT (fun x => (h x : ℂ)) (-Complex.I / 2) =
      ∫ u : ℝ, ((2 * h u * Real.cosh (u / 2) : ℝ) : ℂ) := by
    unfold Zeta23.paperFT
    rw [← MeasureTheory.integral_add hI1 hI2]
    congr 1; ext u
    have ha : Complex.I * (Complex.I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hb' : Complex.I * (-Complex.I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [ha, hb', ← mul_add]
    have h_exp_sum : Complex.exp ((-u / 2 : ℝ) : ℂ) + Complex.exp ((u / 2 : ℝ) : ℂ) =
        ((2 * Real.cosh (u / 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_add]
      congr 1
      rw [Real.cosh_eq]
      ring
    rw [h_exp_sum]
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  have hg_cont : Continuous (fun x => 2 * h x * Real.cosh (x / 2)) :=
    (continuous_const.mul hcont).mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hg_supp_subset : Function.support (fun x => 2 * h x * Real.cosh (x / 2)) ⊆ Set.Icc (-b) b := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra h_not_in
    have h_not_mem : (fun x => (h x : ℂ)) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun x => (h x : ℂ))
      intro hmem
      exact h_not_in (hsupp hmem)
    have h_re_zero : h x = 0 := by
      exact_mod_cast congr_arg Complex.re h_not_mem
    have : 2 * h x * Real.cosh (x / 2) = 0 := by rw [h_re_zero, mul_zero, zero_mul]
    exact hx this
  have hg_c_supp : HasCompactSupport (fun u : ℝ => ((2 * h u * Real.cosh (u / 2) : ℝ) : ℂ)) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    apply hg_supp_subset
    simp only [Function.mem_support, ne_eq]
    intro h_zero
    apply hu
    rw [h_zero, Complex.ofReal_zero]
  have h_c_int : MeasureTheory.Integrable (fun u : ℝ => ((2 * h u * Real.cosh (u / 2) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hg_cont).integrable_of_hasCompactSupport hg_c_supp
  have h_re_step := integral_re h_c_int
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at h_re_step
  rw [step1, ← h_re_step]
  have hg_even : ∀ x, 2 * h (-x) * Real.cosh (-x / 2) = 2 * h x * Real.cosh (x / 2) := by
    intro x
    rw [heven x]
    have : -x / 2 = -(x / 2) := by ring
    rw [this, Real.cosh_neg]
  have h_int_univ : (∫ x in Set.Icc (-b) b, 2 * h x * Real.cosh (x / 2)) =
      ∫ x, 2 * h x * Real.cosh (x / 2) := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra h_nz
    exact hx (hg_supp_subset (Function.mem_support.mpr h_nz))
  have h_int_Icc : (∫ x in Set.Icc (-b) b, 2 * h x * Real.cosh (x / 2)) =
      ∫ x in (-b)..b, 2 * h x * Real.cosh (x / 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc' (x := -b) (y := b)
      (f := fun x => 2 * h x * Real.cosh (x / 2)) Real.volume_singleton
  rw [← h_int_univ, h_int_Icc]
  have hint1 : IntervalIntegrable (fun x => 2 * h x * Real.cosh (x / 2)) MeasureTheory.volume (-b) 0 :=
    hg_cont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => 2 * h x * Real.cosh (x / 2)) MeasureTheory.volume 0 b :=
    hg_cont.intervalIntegrable _ _
  have h_split : (∫ x in (-b)..b, 2 * h x * Real.cosh (x / 2)) =
      (∫ x in (-b)..0, 2 * h x * Real.cosh (x / 2)) + ∫ x in (0 : ℝ)..b, 2 * h x * Real.cosh (x / 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h_symm : (∫ x in (-b)..0, 2 * h x * Real.cosh (x / 2)) =
      ∫ x in (0 : ℝ)..b, 2 * h x * Real.cosh (x / 2) := by
    have h_subst : (∫ x in (0 : ℝ)..b, 2 * h (-x) * Real.cosh (-x / 2)) =
        ∫ x in (-b)..0, 2 * h x * Real.cosh (x / 2) := by
      have h_neg := intervalIntegral.integral_comp_neg (a := 0) (b := b)
        (f := fun x => 2 * h x * Real.cosh (x / 2))
      rw [neg_zero] at h_neg
      exact h_neg
    rw [← h_subst]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact hg_even x
  have h_pull : (∫ x in (0 : ℝ)..b, 2 * h x * Real.cosh (x / 2)) =
      2 * ∫ x in (0 : ℝ)..b, h x * Real.cosh (x / 2) := by
    have : (fun x => 2 * h x * Real.cosh (x / 2)) = fun x => 2 * (h x * Real.cosh (x / 2)) := by
      ext x; ring
    rw [this, intervalIntegral.integral_const_mul]
  rw [h_split, h_symm, h_pull]
  unfold P_pole
  ring

/-! ### Requirement F1: Identification with Literature Gamma Term -/

/-- gammaBracket identity with RH_GammaFinalFormula definitions -/
theorem gammaBracket_eq (r : ℝ) :
    Zeta23.EF.gammaBracket r =
    (Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi := by
  dsimp [Zeta23.EF.gammaBracket, RH_GammaFinalFormula.log_pi]
  congr 2
  push_cast
  ring

/-- F1: The real part of the literature frequency-space Gamma integral equals G_functional -/
theorem G_freq_re_eq_G_functional (h : ℝ → ℝ) (heven : ∀ x, h (-x) = h x) :
    (G_freq (fun x => (h x : ℂ))).re = RH_GammaFinalFormula.G_functional h := by
  dsimp [G_freq, RH_GammaFinalFormula.G_functional]
  have h_ft : ∀ r : ℝ, Zeta23.paperFT (fun u => (h u : ℂ)) r =
      ((RH_GammaFinalFormula.a_func h r : ℝ) : ℂ) := by
    intro r
    have h_symm := Zeta23.Taper.paperFT_ofReal_eq_re (v := h) heven r
    rw [h_symm]
    rfl
  have h_prod : (fun r : ℝ => Zeta23.paperFT (fun u => (h u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)) =
      fun r => (((RH_GammaFinalFormula.a_func h r *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi)) : ℝ) : ℂ) := by
    ext r
    rw [h_ft r, gammaBracket_eq r, ← Complex.ofReal_mul]
  rw [h_prod]
  have h_int : (∫ (r : ℝ), (((RH_GammaFinalFormula.a_func h r *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi)) : ℝ) : ℂ)) =
      (((∫ (r : ℝ), RH_GammaFinalFormula.a_func h r *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi)) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [h_int]
  have h_const : (1 / (2 * π) : ℂ) = (((2 * π)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [one_div]
  rw [h_const]
  rw [← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-! ### Requirement F2: Equivalence of A_arch and A_b -/

/-- F2: The interval-integral Archimedean functional A_arch equals A_b -/
theorem A_arch_eq_A_b (b : ℝ) (hb : 0 < b) (h : ℝ → ℝ) :
    A_arch b h = RH_GammaFinalFormula.A_b h b := by
  dsimp [A_arch, RH_GammaFinalFormula.A_b, RH_GammaFinalFormula.psi_0, RH_GammaFinalFormula.log_pi]
  rw [intervalIntegral.integral_of_le (le_of_lt hb)]
  have h_div : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [h_div]

/-! ### Requirement F3: Elimination of G_eq Hypothesis & Full Real-Space Formula -/

/-- Connecting G_freq real part directly to -A_arch (eliminates G_eq hypothesis) -/
theorem G_freq_re_eq_neg_A_arch (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b) (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    (G_freq (fun x => (h x : ℂ))).re = - A_arch b h := by
  have h_f1 := G_freq_re_eq_G_functional h heven
  have h_gamma := RH_GammaFinalFormula.gamma_eq_neg_A_b h hb hf hsupp heven
  have h_f2 := A_arch_eq_A_b b hb h
  rw [h_f1, h_gamma, h_f2]

/-- F3: Full, unconditioned theorem connecting Zeta23's literatureRHS to W_real.
    All external connection hypotheses (P_eq, S_eq, G_eq) are completely eliminated! -/
theorem literatureRHS_re_eq_W_real (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b)
    (hf : ContDiff ℝ 2 h)
    (heven : ∀ x, h (-x) = h x)
    (hsupp : ∀ x, h x ≠ 0 → |x| ≤ b) :
    (Zeta23.EF.literatureRHS (fun x => (h x : ℂ))).re = W_real b h := by
  have hcont : Continuous h := hf.continuous
  have hsupp_Icc := tsupport_subset_Icc_of_supp_abs_le hsupp
  have P_eq : (Zeta23.paperFT (fun x => (h x : ℂ)) (Complex.I / 2) +
      Zeta23.paperFT (fun x => (h x : ℂ)) (-Complex.I / 2)).re = P_pole b h :=
    pole_term_bridge hb hcont heven hsupp_Icc
  have S_eq : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (((h (Real.log n) : ℝ) : ℂ) + ((h (-Real.log n) : ℝ) : ℂ))).re = S_prime h := by
    have h_bridge := prime_term_bridge hb heven hsupp_Icc
    dsimp [S_prime]
    exact h_bridge
  have G_eq : (G_freq (fun x => (h x : ℂ))).re = -A_arch b h :=
    G_freq_re_eq_neg_A_arch h hb hf hsupp heven
  have h_lit : Zeta23.EF.literatureRHS (fun x => (h x : ℂ)) =
      (Zeta23.paperFT (fun x => (h x : ℂ)) (Complex.I / 2) +
       Zeta23.paperFT (fun x => (h x : ℂ)) (-Complex.I / 2)) -
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (((h (Real.log n) : ℝ) : ℂ) + ((h (-Real.log n) : ℝ) : ℂ))) +
      G_freq (fun x => (h x : ℂ)) := rfl
  rw [h_lit, Complex.add_re, Complex.sub_re]
  rw [P_eq, S_eq, G_eq]
  unfold W_real
  ring

/-! ### Requirement R2: Complex Gamma Integrability -/

/-- R2: Integrability of the literature frequency-space Gamma integrand on ℝ -/
theorem integrable_literature_gamma (h : ℝ → ℝ) {b : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ b) (heven : ∀ u, h (-u) = h u) :
    MeasureTheory.Integrable (fun r : ℝ => Zeta23.paperFT (fun u => (h u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)) := by
  have h_int_real := RH_GammaFinalFormula.integrable_a_mul_digamma_sub_log_pi h hf hsupp
  have h_int_complex : MeasureTheory.Integrable (fun r : ℝ =>
      (((RH_GammaFinalFormula.a_func h r *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp h_int_real
  have h_ft : ∀ r : ℝ, Zeta23.paperFT (fun u => (h u : ℂ)) r =
      ((RH_GammaFinalFormula.a_func h r : ℝ) : ℂ) := by
    intro r
    have h_symm := Zeta23.Taper.paperFT_ofReal_eq_re (v := h) heven r
    rw [h_symm]
    rfl
  have h_prod : (fun r : ℝ => Zeta23.paperFT (fun u => (h u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)) =
      fun r => (((RH_GammaFinalFormula.a_func h r *
        ((Complex.digamma (((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re - RH_GammaFinalFormula.log_pi)) : ℝ) : ℂ) := by
    ext r
    rw [h_ft r, gammaBracket_eq r, ← Complex.ofReal_mul]
  rw [h_prod]
  exact h_int_complex

/-! ### Requirement R3: Connection to Non-trivial Zero Sum -/

/-- R3a: Absolute summability of the non-trivial zeros sum for test functions -/
theorem zeta_zero_sum_summable (h : ℝ → ℝ) {b : ℝ} (hf : ContDiff ℝ 2 h)
    (hsupp : ∀ x, h x ≠ 0 → |x| ≤ b) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT (fun u => (h u : ℂ)) (Zeta23.gammaOf ρ)) := by
  have hk_diff : ContDiff ℝ 2 (fun x => (h x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hk_supp_Icc := tsupport_subset_Icc_of_supp_abs_le hsupp
  have hk_compact : HasCompactSupport (fun x => (h x : ℂ)) :=
    Zeta23.EF.hasCompactSupport_of_tsupport_subset hk_supp_Icc
  exact (Zeta23.WeilEF.EF_lit_zetaZeroConfig (fun x => (h x : ℂ)) hk_diff hk_compact).1

/-- R3b: Main Identity connecting the real part of the non-trivial zeros sum to the real-space Weil formula W_real -/
theorem zeta_zero_sum_re_eq_W_real (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b)
    (hf : ContDiff ℝ 2 h)
    (heven : ∀ x, h (-x) = h x)
    (hsupp : ∀ x, h x ≠ 0 → |x| ≤ b) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT (fun u => (h u : ℂ)) (Zeta23.gammaOf ρ)).re =
    W_real b h := by
  have hk_diff : ContDiff ℝ 2 (fun x => (h x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hk_supp_Icc := tsupport_subset_Icc_of_supp_abs_le hsupp
  have hk_compact : HasCompactSupport (fun x => (h x : ℂ)) :=
    Zeta23.EF.hasCompactSupport_of_tsupport_subset hk_supp_Icc
  have h_ef := (Zeta23.WeilEF.EF_lit_zetaZeroConfig (fun x => (h x : ℂ)) hk_diff hk_compact).2
  have h_re := congrArg Complex.re h_ef
  have h_lit := literatureRHS_re_eq_W_real h hb hf heven hsupp
  rw [h_re, h_lit]


/-! ==========================================================================
  PART E: Real Autocorrelation and Weil Quadratic Form Connection (Task 0081)
  ========================================================================== -/

open scoped ComplexConjugate Convolution

/-- Auxiliary lemma: tilde g = conj(g(-u)) is C^1 if g is C^1. (From 0018 / C1WeilBridge.lean) -/
theorem tilde_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (Zeta23.EF.tilde g) := by
  have hc : ContDiff ℝ 1 (starRingEnd ℂ) := Complex.conjCLE.toContinuousLinearMap.contDiff
  have hneg : ContDiff ℝ 1 (fun x : ℝ => -x) := contDiff_neg
  exact hc.comp (hg.comp hneg)

/-- Regularity lifting for Weil test function: C^1 × C^1 implies C^2 convolution.
    (From 0018 / C1WeilBridge.lean) -/
theorem weilTest_contDiff_of_c1 {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    ContDiff ℝ 2 (Zeta23.EF.weilTest f g) := by
  have h_tilde_supp : HasCompactSupport (Zeta23.EF.tilde g) := Zeta23.EF.hasCompactSupport_tilde hgs
  have h_tilde_c1 : ContDiff ℝ 1 (Zeta23.EF.tilde g) := tilde_contDiff hg
  have h_tilde_loc : LocallyIntegrable (Zeta23.EF.tilde g) volume :=
    (Zeta23.EF.continuous_tilde hg.continuous).locallyIntegrable
  have h_hasDerivAt : ∀ x : ℝ, HasDerivAt (Zeta23.EF.weilTest f g)
      ((deriv f ⋆[ContinuousLinearMap.mul ℝ ℂ] Zeta23.EF.tilde g) x) x := by
    intro x
    exact hfs.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hf h_tilde_loc x
  have h_diff : Differentiable ℝ (Zeta23.EF.weilTest f g) := fun x => (h_hasDerivAt x).differentiableAt
  have h_deriv_eq : deriv (Zeta23.EF.weilTest f g) = deriv f ⋆[ContinuousLinearMap.mul ℝ ℂ] Zeta23.EF.tilde g := by
    ext x
    exact (h_hasDerivAt x).deriv
  have hf_deriv_cont : Continuous (deriv f) := hf.continuous_deriv_one
  have hf_deriv_loc : LocallyIntegrable (deriv f) volume := hf_deriv_cont.locallyIntegrable
  have h_deriv_c1 : ContDiff ℝ 1 (deriv f ⋆[ContinuousLinearMap.mul ℝ ℂ] Zeta23.EF.tilde g) := by
    have h_right := h_tilde_supp.contDiff_convolution_right (n := 1)
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) hf_deriv_loc h_tilde_c1
    exact h_right
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (Zeta23.EF.weilTest f g)
  rw [contDiff_succ_iff_deriv]
  refine ⟨h_diff, by intro h_top; contradiction, ?_⟩
  rw [h_deriv_eq]
  exact h_deriv_c1

/-- Full-zero Weil bridge for C^1 compactly supported test functions on general zero config Z with EF_lit Z.
    (From 0018 / C1WeilBridge.lean) -/
theorem weil_bridge_of_c1 (Z : Zeta23.ZeroConfig) (hEF : Zeta23.EF.EF_lit Z)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Summable (fun ρ : Z.carrier => Z.Wsummand f g (ρ : ℂ)) ∧
    Z.W f g = Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) := by
  have hk : ContDiff ℝ 2 (Zeta23.EF.weilTest f g) := weilTest_contDiff_of_c1 hf hg hfc hgc
  obtain ⟨hsum, heq⟩ := hEF (Zeta23.EF.weilTest f g) hk (Zeta23.EF.weilTest_hasCompactSupport hfc hgc)
  have hfac : ∀ z : ℂ, Zeta23.paperFT (Zeta23.EF.weilTest f g) z =
      Zeta23.paperFT f z * (starRingEnd ℂ) (Zeta23.paperFT g ((starRingEnd ℂ) z)) :=
    Zeta23.EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hterm : (fun ρ : Z.carrier => (Z.mult (ρ : ℂ) : ℂ) * Zeta23.paperFT (Zeta23.EF.weilTest f g) (Zeta23.gammaOf (ρ : ℂ)))
      = fun ρ : Z.carrier => Z.Wsummand f g (ρ : ℂ) := by
    ext ρ
    simp only [Zeta23.ZeroConfig.Wsummand, hfac, mul_assoc]
  have hsum_w : Summable (fun ρ : Z.carrier => Z.Wsummand f g (ρ : ℂ)) := hterm ▸ hsum
  have heq_w : Z.W f g = Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) := by
    rw [Zeta23.ZeroConfig.W]
    rw [← hterm]
    exact heq
  exact ⟨hsum_w, heq_w⟩

/-- Concrete Weil bridge for C^1 compactly supported test functions on Riemann zeta zeros.
    (From 0018 / C1WeilBridge.lean) -/
theorem weil_bridge_zetaZeroConfig_of_c1
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f g (ρ : ℂ)) ∧
    Zeta23.zetaZeroConfig.W f g = Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) :=
  weil_bridge_of_c1 Zeta23.zetaZeroConfig Zeta23.WeilEF.EF_lit_zetaZeroConfig hf hg hfc hgc

/-! ### Requirement S1: Real Autocorrelation Function -/

/-- Explicit definition of real autocorrelation h_f(x) = ∫ f(t) f(t - x) dt -/
noncomputable def real_autocorr (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f t * f (t - x)

/-- Auxiliary theorem for coercing real integral to complex integral -/
theorem integral_ofReal_C (g : ℝ → ℝ) : ∫ x, (g x : ℂ) = ((∫ x, g x : ℝ) : ℂ) :=
  integral_ofReal

/-- S1.1: Identification of real autocorrelation with Zeta23 weilTest -/
theorem real_autocorr_eq_weilTest (f : ℝ → ℝ) :
    (fun x => (real_autocorr f x : ℂ)) =
    Zeta23.EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) := by
  ext x
  unfold Zeta23.EF.weilTest Zeta23.EF.tilde real_autocorr
  rw [convolution_def]
  have h_int : (∫ t, ContinuousLinearMap.mul ℝ ℂ (f t : ℂ) (starRingEnd ℂ (f (-(x - t)) : ℂ))) =
      ∫ t, (((f t * f (t - x) : ℝ) : ℂ)) := by
    congr 1; ext t
    have h1 : -(x - t) = t - x := by ring
    rw [h1, Complex.conj_ofReal]
    dsimp [ContinuousLinearMap.mul]
    rw [← Complex.ofReal_mul]
  rw [h_int]
  exact (integral_ofReal_C (fun t => f t * f (t - x))).symm

/-- Compact support of fC from pointwise support bound -/
lemma hasCompactSupport_of_supp_abs_le {f : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ L) :
    HasCompactSupport (fun x => (f x : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  have h_re : f x ≠ 0 := by
    intro hzero
    apply hx
    rw [hzero, Complex.ofReal_zero]
  have h_abs := hsupp x h_re
  rw [Set.mem_Icc]
  exact abs_le.mp h_abs

/-- S1.2: C^2 regularity of the real autocorrelation for any C^1 test function -/
theorem real_autocorr_contDiff {f : ℝ → ℝ} {L : ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : ∀ x, f x ≠ 0 → |x| ≤ L) :
    ContDiff ℝ 2 (real_autocorr f) := by
  have hfC_diff : ContDiff ℝ 1 (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfC_supp : HasCompactSupport (fun x => (f x : ℂ)) :=
    hasCompactSupport_of_supp_abs_le hsupp
  have h_weil_diff : ContDiff ℝ 2 (Zeta23.EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ))) :=
    weilTest_contDiff_of_c1 hfC_diff hfC_diff hfC_supp hfC_supp
  have h_eq := real_autocorr_eq_weilTest f
  have h_c_diff : ContDiff ℝ 2 (fun x => (real_autocorr f x : ℂ)) := by
    rw [h_eq]
    exact h_weil_diff
  have h_re_diff : ContDiff ℝ 2 (fun x => Complex.reCLM (real_autocorr f x : ℂ)) :=
    Complex.reCLM.contDiff.comp h_c_diff
  exact h_re_diff

/-- S1.3: Parity (evenness) of the real autocorrelation without any parity hypothesis on f -/
theorem real_autocorr_even (f : ℝ → ℝ) (x : ℝ) :
    real_autocorr f (-x) = real_autocorr f x := by
  unfold real_autocorr
  have h1 : (∫ t, f t * f (t - -x)) = ∫ t, f t * f (t + x) := by
    congr 1; ext t; rw [sub_neg_eq_add]
  rw [h1]
  have h2 : (∫ t, f t * f (t + x)) = ∫ u, f (u - x) * f u := by
    rw [← MeasureTheory.integral_add_right_eq_self (fun u => f (u - x) * f u) x]
    congr 1; ext t
    have : t + x - x = t := by ring
    rw [this, mul_comm]
  rw [h2]
  congr 1; ext u
  exact mul_comm (f (u - x)) (f u)

/-- S1.4: Support bound |x| ≤ 2L for the real autocorrelation -/
theorem real_autocorr_supp_bound {f : ℝ → ℝ} {L : ℝ} (_hL : 0 < L)
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ L) (x : ℝ) (hx : real_autocorr f x ≠ 0) :
    |x| ≤ 2 * L := by
  have hfC_tsupp : tsupport (fun x => (f x : ℂ)) ⊆ Set.Icc (-L) L :=
    tsupport_subset_Icc_of_supp_abs_le hsupp
  have h_L2 : (2 * L) / 2 = L := by ring
  have hfC_tsupp_halved : tsupport (fun x => (f x : ℂ)) ⊆ Set.Icc (-((2 * L) / 2)) ((2 * L) / 2) := by
    intro y hy
    have := hfC_tsupp hy
    rw [Set.mem_Icc] at this ⊢
    constructor
    · linarith [this.1, h_L2]
    · linarith [this.2, h_L2]
  have h_weil_tsupp := Zeta23.EF.tsupport_weilTest_subset hfC_tsupp_halved hfC_tsupp_halved
  have h_eq := real_autocorr_eq_weilTest f
  have h_mem_supp : x ∈ Function.support (fun x => (real_autocorr f x : ℂ)) := by
    simp only [Function.mem_support, ne_eq]
    intro h_zero
    apply hx
    exact_mod_cast congrArg Complex.re h_zero
  have h_mem_tsupp : x ∈ tsupport (fun x => (real_autocorr f x : ℂ)) :=
    subset_tsupport _ h_mem_supp
  rw [h_eq] at h_mem_tsupp
  have h_icc := h_weil_tsupp h_mem_tsupp
  rw [Set.mem_Icc] at h_icc
  exact abs_le.mpr h_icc

/-! ### Requirement S2: Weil Quadratic Form Connection -/

/-- S2: The real part of the full-zero Weil quadratic form equals W_real(2L, h_f),
    with summability over non-trivial zeros established unconditionally. -/
theorem weil_quad_form_re_eq_W_real (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ L) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) (ρ : ℂ)) ∧
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
    W_real (2 * L) (real_autocorr f) := by
  have hfC_diff : ContDiff ℝ 1 (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfC_supp : HasCompactSupport (fun x => (f x : ℂ)) :=
    hasCompactSupport_of_supp_abs_le hsupp
  have h_bridge := weil_bridge_zetaZeroConfig_of_c1 hfC_diff hfC_diff hfC_supp hfC_supp
  have h_summable := h_bridge.1
  have h_W_eq := h_bridge.2
  have h_W_re : (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      (Zeta23.EF.literatureRHS (Zeta23.EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ)))).re := by
    rw [h_W_eq]
  have h_test_eq := real_autocorr_eq_weilTest f
  have h_c2 : ContDiff ℝ 2 (real_autocorr f) := real_autocorr_contDiff hf hsupp
  have h_even : ∀ x, real_autocorr f (-x) = real_autocorr f x := real_autocorr_even f
  have h_2L_pos : 0 < 2 * L := by linarith
  have h_autocorr_supp : ∀ x, real_autocorr f x ≠ 0 → |x| ≤ 2 * L :=
    real_autocorr_supp_bound hL hsupp
  have h_lit_re := literatureRHS_re_eq_W_real (real_autocorr f) h_2L_pos h_c2 h_even h_autocorr_supp
  rw [← h_test_eq] at h_W_re
  rw [h_lit_re] at h_W_re
  exact ⟨h_summable, h_W_re⟩

end RH_LiteratureBridge
