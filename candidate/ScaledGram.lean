import LegendreContract

open Polynomial MeasureTheory Set
namespace RHLegendreContract

noncomputable def scaledQ (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt ((2*(n:ℝ)+1)/(2*L)) * (Q n).eval (1/2-x/(2*L))

lemma affine_integral {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    (∫ x in -L..L, f (1/2-x/(2*L))) = (2*L) * ∫ t in (0:ℝ)..1, f t := by
  have hn : 2*L ≠ 0 := ne_of_gt (by positivity)
  have h0 : (1:ℝ)/2-L/(2*L) = 0 := by field_simp; ring
  have h1 : (1:ℝ)/2-(-L)/(2*L) = 1 := by field_simp; ring
  have h := intervalIntegral.integral_comp_sub_div f (a := -L) (b := L) hn ((1:ℝ)/2)
  simpa only [h0,h1,smul_eq_mul] using h

/-- Conditional form: the unit-interval Gram formula is a hypothesis of this theorem. -/
theorem scaled_gram_of_unit_gram {L : ℝ} (hL : 0 < L)
    (hgram : ∀ m n : ℕ, (∫ t in (0:ℝ)..1, (Q m).eval t * (Q n).eval t) =
      if m=n then 1/(2*(n:ℝ)+1) else 0) (m n : ℕ) :
    (∫ x in -L..L, scaledQ L m x * scaledQ L n x) = if m=n then 1 else 0 := by
  have he : (fun x : ℝ => scaledQ L m x * scaledQ L n x) =
      (fun x : ℝ => (Real.sqrt ((2*(m:ℝ)+1)/(2*L))*Real.sqrt ((2*(n:ℝ)+1)/(2*L))) *
        ((Q m).eval (1/2-x/(2*L)) * (Q n).eval (1/2-x/(2*L)))) := by
    funext x
    unfold scaledQ
    ring
  rw [he, intervalIntegral.integral_const_mul, affine_integral hL (fun t => (Q m).eval t * (Q n).eval t), hgram]
  by_cases hmn : m=n
  · subst m
    simp only [↓reduceIte]
    calc
      _ = (Real.sqrt ((2*(n:ℝ)+1)/(2*L)))^2 * ((2*L)/(2*(n:ℝ)+1)) := by ring
      _ = 1 := by
        rw [Real.sq_sqrt (by positivity)]
        field_simp
  · simp [hmn]

end RHLegendreContract
