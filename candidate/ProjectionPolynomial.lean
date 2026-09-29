import PolynomialLpMap
import ExpectedActual
open MeasureTheory Set
namespace RHProjectionPolynomial
open RHLegendreDirections RHPolynomialLpMap

noncomputable def poly {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : Polynomial ℂ :=
  ∑ n ∈ s, inner ℂ (direction L hL.le n) f • directionPoly L n

theorem toLp_poly {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    toLp L hL.le (poly hL s f) =
      RHFiniteProjection.finiteProjection s (direction L hL.le) f := by
  rw [RHExpected0252.projection_coefficients L hL s f]
  simp only [poly, map_sum, map_smul, toLp_directionPoly]

theorem coefficient_preserved {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (n : ℕ) (hn : n ∈ s) :
    inner ℂ (direction L hL.le n) (toLp L hL.le (poly hL s f)) =
      inner ℂ (direction L hL.le n) f := by
  rw [toLp_poly, RHExpected0252.projection_coefficients L hL s f]
  simp only [inner_sum, inner_smul_right, RHExpected0252.direction_inner L hL]
  simp [hn]

theorem inner_integral {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (p : Polynomial ℂ) :
    inner ℂ f (toLp L hL.le p) =
      ∫ x in Icc (-L) L, star (f x) * p.eval (x : ℂ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_poly hL.le p] with x hx
  change inner ℂ (f x) (RHBoundedWindow.intervalPolynomial L hL.le p x) = _
  rw [hx]
  exact RCLike.inner_apply' (f x) (p.eval (x : ℂ))
end RHProjectionPolynomial
