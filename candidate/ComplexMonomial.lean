import TuckIntegral
open MeasureTheory Set intervalIntegral
namespace RHTuckComplex

lemma real_integrable (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun y : ℝ => (x^n-y^n)/|x-y|) volume (-1) 1 := by
  have hd : Continuous (RHDividedMoments.difference n x) := by
    unfold RHDividedMoments.difference; fun_prop
  have hl : IntervalIntegrable (fun y : ℝ => (x^n-y^n)/|x-y|) volume (-1) x := by
    apply (hd.intervalIntegrable (-1) x).congr_uIoo
    rw [uIoo_of_le hx.1]
    intro y hy
    exact (RHDividedMoments.left_quotient n hy.2).symm
  have hr : IntervalIntegrable (fun y : ℝ => (x^n-y^n)/|x-y|) volume x 1 := by
    apply (hd.neg.intervalIntegrable x 1).congr_uIoo
    rw [uIoo_of_le hx.2]
    intro y hy
    exact (RHDividedMoments.right_quotient n hy.1).symm
  exact hl.trans hr

lemma complex_integrable (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun y : ℝ => ((x:ℂ)^n-(y:ℂ)^n)/((|x-y|:ℝ):ℂ)) volume (-1) 1 := by
  have h := real_integrable n hx
  have hc : IntervalIntegrable (fun y : ℝ => (((x^n-y^n)/|x-y| : ℝ):ℂ)) volume (-1) 1 :=
    ⟨h.1.ofReal,h.2.ofReal⟩
  simpa only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow] using hc

theorem complex_integral (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∫ y in (-1 : ℝ)..1, ((x:ℂ)^n-(y:ℂ)^n)/((|x-y|:ℝ):ℂ)) =
      (RHTuckMonomial.image n).eval (x:ℂ) := by
  have h := RHTuckIntegral.monomial_integral n hx
  rw [← intervalIntegral.integral_ofReal] at h
  simpa only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow] using h
end RHTuckComplex
