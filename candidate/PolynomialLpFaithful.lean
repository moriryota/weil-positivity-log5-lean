import PolynomialLpMap
import DirectionSpan
import ActualDirections
import PolynomialSymmetry
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHTuckLp
open RHPolynomialLpMap RHLegendreDirections

theorem toLp_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (toLp L hL.le) := by
  apply LinearMap.injective_of_linearIndependent (RHDirectionSpan.span_directionPoly hL)
  exact (RHLegendreActual.directions_orthonormal hL).linearIndependent

theorem inner_eq_integral {L : ℝ} (hL : 0 ≤ L) (p q : Polynomial ℂ) :
    inner ℂ (toLp L hL p) (toLp L hL q) =
      ∫ x in Icc (-L) L, conj (p.eval (x:ℂ)) * q.eval (x:ℂ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_poly hL p,coe_poly hL q] with x hp hq
  change ((toLp L hL p : ℝ → ℂ) x) = p.eval (x:ℂ) at hp
  change ((toLp L hL q : ℝ → ℂ) x) = q.eval (x:ℂ) at hq
  rw [hp,hq]
  simp [RCLike.inner_apply, mul_comm]

theorem unit_hermitian (p q : Polynomial ℂ) :
    inner ℂ (toLp 1 (by norm_num) p) (toLp 1 (by norm_num) (RHTuckLinear.operator q)) =
      inner ℂ (toLp 1 (by norm_num) (RHTuckLinear.operator p)) (toLp 1 (by norm_num) q) := by
  rw [inner_eq_integral,← inner_conj_symm,inner_eq_integral]
  exact RHTuckPolynomial.operator_hermitian p q
end RHTuckLp
