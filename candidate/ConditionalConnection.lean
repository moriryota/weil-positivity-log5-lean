import LegendreBase
import RecurrenceAdapter
import ScaledGram
import L2GramAdapter
import ProjectionCoefficients

open MeasureTheory Set
open scoped BigOperators
namespace RHLegendreContract

/-- Conditional form: the polynomial recurrence and the unit Gram identities are hypotheses of this theorem. -/
theorem directions_orthonormal_of_unit_data
    (hr : ∀ n : ℕ, Polynomial.C ((n:ℝ)+2)*Q (n+2) =
      Polynomial.C (2*(n:ℝ)+3)*(1-Polynomial.C 2*Polynomial.X)*Q (n+1) -
        Polynomial.C ((n:ℝ)+1)*Q n)
    (hg : ∀ m n : ℕ, (∫ t in (0:ℝ)..1, (Q m).eval t*(Q n).eval t) =
      if m=n then 1/(2*(n:ℝ)+1) else 0)
    {L : ℝ} (hL : 0 < L) : Orthonormal ℂ (RHLegendreDirections.direction L hL.le) := by
  apply orthonormal_of_real_gram hL.le (RHLegendreDirections.direction L hL.le) (scaledQ L)
  · intro n
    have h := RHLegendreDirections.direction_coe_ae hL.le n
    filter_upwards [h] with x hx
    rw [hx, recPoly_eval_eq_Q_of_recurrence Q_zero_base Q_one_base hr hL n x]
    simp only [scaledQ, Complex.ofReal_mul]
  · exact scaled_gram_of_unit_gram hL hg

theorem direction_projection_eq_sum_of_unit_data
    (hr : ∀ n : ℕ, Polynomial.C ((n:ℝ)+2)*Q (n+2) =
      Polynomial.C (2*(n:ℝ)+3)*(1-Polynomial.C 2*Polynomial.X)*Q (n+1) -
        Polynomial.C ((n:ℝ)+1)*Q n)
    (hg : ∀ m n : ℕ, (∫ t in (0:ℝ)..1, (Q m).eval t*(Q n).eval t) =
      if m=n then 1/(2*(n:ℝ)+1) else 0)
    {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    RHFiniteProjection.finiteProjection s (RHLegendreDirections.direction L hL.le) f =
      ∑ n ∈ s, inner ℂ (RHLegendreDirections.direction L hL.le n) f •
        RHLegendreDirections.direction L hL.le n :=
  RHFiniteProjection.finiteProjection_eq_sum s _ (directions_orthonormal_of_unit_data hr hg hL) f

end RHLegendreContract
