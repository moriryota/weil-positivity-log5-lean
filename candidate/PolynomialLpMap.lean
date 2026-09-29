import RecurrenceBasis
open MeasureTheory Set
namespace RHPolynomialLpMap
open RHBoundedWindow RHLegendreDirections

lemma coe_poly {L : ℝ} (hL : 0 ≤ L) (P : Polynomial ℂ) :
    (intervalPolynomial L hL P : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x : ℝ => P.eval (x:ℂ)) := MemLp.coeFn_toLp (polynomial_memLp hL P)

noncomputable def toLp (L : ℝ) (hL : 0 ≤ L) :
    Polynomial ℂ →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Icc (-L) L)) where
  toFun := intervalPolynomial L hL
  map_add' P Q := by
    apply Lp.ext
    filter_upwards [coe_poly hL (P+Q), coe_poly hL P, coe_poly hL Q,
      Lp.coeFn_add (intervalPolynomial L hL P) (intervalPolynomial L hL Q)] with x hsum hp hq hadd
    rw [hsum, hadd, Pi.add_apply, hp, hq, Polynomial.eval_add]
  map_smul' c P := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [coe_poly hL (c • P), coe_poly hL P,
      Lp.coeFn_smul c (intervalPolynomial L hL P)] with x hcp hp hsmul
    rw [hcp, hsmul, Pi.smul_apply, hp, Polynomial.eval_smul]

lemma toLp_directionPoly {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    toLp L hL (directionPoly L n) = direction L hL n := rfl
end RHPolynomialLpMap
