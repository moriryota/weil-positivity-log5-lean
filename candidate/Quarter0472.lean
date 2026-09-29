import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Tactic
namespace Trial0456
 theorem digamma_quarter_re : (Complex.digamma (1/4 : ℂ)).re =
    -Real.eulerMascheroniConstant - Real.pi/2 - 3*Real.log 2 := by
  have hi : ∀ n : ℤ, (1/4 : ℂ) ≠ n := by
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn' : (1 : ℝ) = 4 * (n : ℝ) := by linarith
    have hz : (1 : ℤ) = 4 * n := by exact_mod_cast hn'
    omega
  have hp : ∀ m : ℕ, 2 * (1/4 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hr := congrArg Complex.re hm
    norm_num at hr
    have hnon : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hc : Complex.cot ((Real.pi : ℂ) * (1/4 : ℂ)) = 1 := by
    rw [show (Real.pi : ℂ) * (1/4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cot]
    norm_cast
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    exact div_self (by positivity)
  have hreflection := Complex.digamma_one_sub hi
  have hduplication := Complex.digamma_two_mul hp
  norm_num at hreflection hduplication
  rw [hc] at hreflection
  have hhalf := Complex.digamma_one_half
  have h1 := congrArg Complex.re hreflection
  have h2 := congrArg Complex.re hduplication
  have h3 := congrArg Complex.re hhalf
  norm_num [Complex.mul_re, Complex.log_re] at h1 h2 h3
  linarith
end Trial0456
