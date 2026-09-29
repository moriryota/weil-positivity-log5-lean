import ColDecomp0499
import Leg0503

/-! # 0505: link of the repository basis to Legendre polynomials on [-1,1]; orthogonality

* `(recPoly n).eval x = p n (x / L)` (`L = halfWidth`);
* `(basisPoly n).eval x = √((2n+1)/(2L)) · p n (x / L)`;
* `∫_{−1}^1 p n · p k = if n = k then 2/(2n+1) else 0` (from `gram`, by scaling). -/

open MeasureTheory Set
open scoped BigOperators

namespace RHLink0505
open RHConditionalLog5 RHLog5Bridge RHLeg0503

lemma recPoly_eval : ∀ (n : ℕ) (x : ℝ), (recPoly n).eval x = p n (x / halfWidth)
  | 0, x => by simp [recPoly, p_zero]
  | 1, x => by simp [recPoly, p_one]; ring
  | n + 2, x => by
      have hL := halfWidth_pos
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      have h := p_rec n (x / halfWidth)
      simp only [recPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        recPoly_eval (n + 1) x, recPoly_eval n x]
      apply mul_left_cancel₀ hn
      rw [h]
      field_simp

lemma basisPoly_eval (n : ℕ) (x : ℝ) :
    (basisPoly n).eval x = Real.sqrt ((2 * n + 1) / (2 * halfWidth)) * p n (x / halfWidth) := by
  simp [basisPoly, recPoly_eval]

theorem orth (n k : ℕ) :
    ∫ u in (-1:ℝ)..1, p n u * p k u = if n = k then (2 : ℝ) / (2 * n + 1) else 0 := by
  have hL := halfWidth_pos
  have g := RHColDecomp0499.gram n k
  rw [RHEntry00_0495.setI] at g
  simp only [basisPoly_eval] at g
  have e : (∫ x in (-halfWidth)..halfWidth,
      Real.sqrt ((2 * n + 1) / (2 * halfWidth)) * p n (x / halfWidth) *
        (Real.sqrt ((2 * k + 1) / (2 * halfWidth)) * p k (x / halfWidth))) =
      Real.sqrt ((2 * n + 1) / (2 * halfWidth)) * Real.sqrt ((2 * k + 1) / (2 * halfWidth)) *
        (halfWidth * ∫ u in (-1:ℝ)..1, p n u * p k u) := by
    have h := intervalIntegral.integral_comp_div (a := -halfWidth) (b := halfWidth)
      (fun u => p n u * p k u) hL.ne'
    rw [neg_div, div_self hL.ne', smul_eq_mul] at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [e] at g
  have hsn : 0 < Real.sqrt ((2 * n + 1) / (2 * halfWidth)) := Real.sqrt_pos.mpr (by positivity)
  have hsk : 0 < Real.sqrt ((2 * k + 1) / (2 * halfWidth)) := Real.sqrt_pos.mpr (by positivity)
  split_ifs with hnk
  · subst hnk
    rw [if_pos rfl] at g
    have hsq : Real.sqrt ((2 * n + 1) / (2 * halfWidth)) * Real.sqrt ((2 * n + 1) / (2 * halfWidth)) =
        (2 * n + 1) / (2 * halfWidth) := Real.mul_self_sqrt (by positivity)
    rw [hsq] at g
    have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp at g
    rw [eq_div_iff h2]
    simp only [← sq]
    linarith
  · rw [if_neg hnk] at g
    have := mul_eq_zero.mp g
    rcases this with h | h
    · exact absurd h (mul_pos hsn hsk).ne'
    · exact (mul_eq_zero.mp h).resolve_left hL.ne'

end RHLink0505

