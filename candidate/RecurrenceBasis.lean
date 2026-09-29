import Final
import FiniteCorrection

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace RHLegendreDirections
open RHFormDomain RHBoundedWindow

/-- Exactly the unnormalised recurrence used by the numerical certificate.
This definition does not assert orthogonality. -/
noncomputable def recPoly (L : ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (1/(L:ℂ)) * Polynomial.X
  | n+2 => (Polynomial.X * recPoly L (n+1) * Polynomial.C ((2*(n:ℂ)+3)/(L:ℂ)) -
      recPoly L n * Polynomial.C ((n:ℂ)+1)) * Polynomial.C (1/((n:ℂ)+2))

lemma recPoly_zero (L : ℝ) : recPoly L 0 = 1 := rfl
lemma recPoly_one (L : ℝ) : recPoly L 1 = Polynomial.C (1/(L:ℂ))*Polynomial.X := rfl

lemma recPoly_eval_step (L : ℝ) (n : ℕ) (x : ℂ) :
    (recPoly L (n+2)).eval x =
      (x * (recPoly L (n+1)).eval x * ((2*(n:ℂ)+3)/(L:ℂ)) -
        (recPoly L n).eval x * ((n:ℂ)+1)) * (1/((n:ℂ)+2)) := by
  rw [recPoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

noncomputable def directionPoly (L : ℝ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.C ((Real.sqrt ((2*(n:ℝ)+1)/(2*L)) : ℝ) : ℂ) * recPoly L n

lemma directionPoly_eval (L : ℝ) (n : ℕ) (x : ℝ) :
    (directionPoly L n).eval (x:ℂ) =
      ((Real.sqrt ((2*(n:ℝ)+1)/(2*L)) : ℝ) : ℂ) * (recPoly L n).eval (x:ℂ) := by
  simp only [directionPoly, Polynomial.eval_mul, Polynomial.eval_C]

noncomputable def direction (L : ℝ) (hL : 0 ≤ L) (n : ℕ) :
    Lp ℂ 2 (volume.restrict (Icc (-L) L)) := intervalPolynomial L hL (directionPoly L n)

theorem direction_mem {L : ℝ} (hL : 0 ≤ L) (n : ℕ) : InDomain L (direction L hL n) :=
  intervalPolynomial_mem hL (directionPoly L n)

lemma direction_coe_ae {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    (direction L hL n : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x : ℝ => ((Real.sqrt ((2*(n:ℝ)+1)/(2*L)) : ℝ) : ℂ) * (recPoly L n).eval (x:ℂ)) := by
  have h := MemLp.coeFn_toLp (polynomial_memLp hL (directionPoly L n))
  simpa only [direction, intervalPolynomial, directionPoly_eval] using h

/-- Finite linear combinations; no claim yet that these are orthogonal projections. -/
theorem finite_sum_mem {L : ℝ} (hL : 0 ≤ L) (s : Finset ℕ) (c : ℕ → ℂ) :
    InDomain L (∑ n ∈ s, c n • direction L hL n) := by
  exact (formSubmodule L).sum_mem (fun n _ => (formSubmodule L).smul_mem (c n) (direction_mem hL n))

theorem residual_mem {L : ℝ} (hL : 0 ≤ L) (s : Finset ℕ) (c : ℕ → ℂ)
    {f : Lp ℂ 2 (volume.restrict (Icc (-L) L))} (hf : InDomain L f) :
    InDomain L (f - ∑ n ∈ s, c n • direction L hL n) :=
  finite_correction_mem s (direction L hL) (fun n _ => direction_mem hL n) c hf

end RHLegendreDirections
