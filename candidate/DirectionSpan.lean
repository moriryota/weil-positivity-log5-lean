import RecurrenceBasis
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Algebraic span of the real-direction polynomials

We show that the family `RHLegendreDirections.directionPoly L` (for `0 < L`) spans the whole
polynomial ring `ℂ[X]` as a `ℂ`-submodule.

The key input is `Polynomial.Sequence.span`: a sequence of polynomials whose `i`-th member has
degree `i` and unit leading coefficient spans `ℂ[X]`.  So the entire proof reduces to computing
`(directionPoly L n).degree = n`, which in turn reduces to `(recPoly L n).degree = n`.
-/

open Polynomial

namespace RHLegendreDirections

/-- The unnormalised recurrence polynomial `recPoly L n` has degree exactly `n`, provided `L ≠ 0`.
The proof is a two–step induction following the three branches of `recPoly`. -/
lemma recPoly_degree {L : ℝ} (hL : L ≠ 0) (n : ℕ) : (recPoly L n).degree = (n : ℕ) := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  induction n using Nat.twoStepInduction with
  | zero => simp [recPoly_zero]
  | one =>
      rw [recPoly_one, degree_C_mul_X (one_div_ne_zero hLC)]
      norm_cast
  | more n ih1 ih2 =>
      have ha : (2 * (n : ℂ) + 3) / (L : ℂ) ≠ 0 := by
        refine div_ne_zero ?_ hLC
        have h : (2 * (n : ℂ) + 3) = ((2 * n + 3 : ℕ) : ℂ) := by push_cast; ring
        rw [h]; exact Nat.cast_ne_zero.mpr (by omega)
      have hb : ((n : ℂ) + 1) ≠ 0 := by
        have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [h]; exact Nat.cast_ne_zero.mpr (by omega)
      have hc : (1 / ((n : ℂ) + 2)) ≠ 0 := by
        refine one_div_ne_zero ?_
        have h : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [h]; exact Nat.cast_ne_zero.mpr (by omega)
      rw [recPoly, degree_mul_C hc, degree_sub_eq_left_of_degree_lt,
          degree_mul_C ha, mul_comm X (recPoly L (n + 1)), degree_mul_X, ih2]
      · norm_cast
      · rw [degree_mul_C hb, ih1, degree_mul_C ha, mul_comm X (recPoly L (n + 1)),
            degree_mul_X, ih2]
        exact_mod_cast (show n < n + 1 + 1 by omega)

/-- The normalised real-direction polynomial `directionPoly L n` also has degree exactly `n`
whenever `0 < L`: the normalisation constant `√((2n+1)/(2L))` is a nonzero real. -/
lemma directionPoly_degree {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (directionPoly L n).degree = (n : ℕ) := by
  have hpos : (0 : ℝ) < (2 * (n : ℝ) + 1) / (2 * L) := by
    apply div_pos
    · positivity
    · linarith
  have hs : Real.sqrt ((2 * (n : ℝ) + 1) / (2 * L)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsC : ((Real.sqrt ((2 * (n : ℝ) + 1) / (2 * L)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs
  simp only [directionPoly]
  rw [degree_C_mul hsC, recPoly_degree hL.ne' n]

end RHLegendreDirections

namespace RHDirectionSpan

open RHLegendreDirections

/-- The real-direction polynomials, packaged as a `Polynomial.Sequence ℂ`
(the `n`-th entry has degree `n`). -/
noncomputable def directionSeq {L : ℝ} (hL : 0 < L) : Polynomial.Sequence ℂ where
  elems' := directionPoly L
  degree_eq' n := directionPoly_degree hL n

/-- The real-direction polynomials span all of `ℂ[X]` as a `ℂ`-submodule. -/
theorem span_directionPoly {L : ℝ} (hL : 0 < L) :
    Submodule.span ℂ (Set.range (RHLegendreDirections.directionPoly L)) = ⊤ := by
  have hunit : ∀ i, IsUnit ((directionSeq hL) i).leadingCoeff := fun i =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr ((directionSeq hL).ne_zero i))
  exact (directionSeq hL).span hunit


end RHDirectionSpan
