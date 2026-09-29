import TuckLinear
import DirectionSpan
open Polynomial
namespace RHTuckResidual

theorem residual_degree (p : Polynomial ℂ) (n : ℕ) (hp : p.degree = (n:ℕ)) :
    (RHTuckLinear.operator p - (2*(harmonic n:ℂ)) • p).degree < (n:ℕ) := by
  have hn : p.natDegree = n := natDegree_eq_of_degree_eq_some hp
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_sub,Polynomial.coeff_smul,smul_eq_mul]
  rcases eq_or_lt_of_le hm with h | h
  · subst m
    rw [← hn,RHTuckLinear.coeff_diag]
    ring
  · rw [RHTuckLinear.coeff_above p m (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem span_low {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Submodule.span ℂ ((RHLegendreDirections.directionPoly L) '' Set.Iio n) =
      Polynomial.degreeLT ℂ n := by
  exact (RHDirectionSpan.directionSeq hL).span_degreeLT (fun i hi =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
      ((RHDirectionSpan.directionSeq hL).ne_zero i)))
end RHTuckResidual
