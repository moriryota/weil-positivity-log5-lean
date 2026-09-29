import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
open Set Polynomial
namespace RHComplexApprox

/-- Real and imaginary approximants share an explicit half-error budget. -/
theorem exists_complex_polynomial_near (a b : ℝ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ x ∈ Icc a b, ‖P.eval (x:ℂ) - f x‖ < ε := by
  have hr : ContinuousOn (fun x => (f x).re) (Icc a b) := Complex.continuous_re.comp_continuousOn hf
  have hi : ContinuousOn (fun x => (f x).im) (Icc a b) := Complex.continuous_im.comp_continuousOn hf
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b _ hr (ε/2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b _ hi (ε/2) (by positivity)
  let P : Polynomial ℂ := p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom
  refine ⟨P, ?_⟩
  intro x hx
  have he : P.eval (x:ℂ) = ((p.eval x:ℝ):ℂ) + Complex.I*((q.eval x:ℝ):ℂ) := by
    have heval (r : Polynomial ℝ) : (r.map Complex.ofRealHom).eval (x:ℂ) = ((r.eval x:ℝ):ℂ) :=
      Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := r) x
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, heval]
  rw [he]
  have hn := Complex.norm_le_abs_re_add_abs_im (((p.eval x:ℝ):ℂ) + Complex.I*((q.eval x:ℝ):ℂ) - f x)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul, zero_add] at hn
  exact hn.trans_lt (by linarith [hp x hx, hq x hx])
end RHComplexApprox
