import PolynomialLpFaithful
import TuckPreserves
import TuckResidual
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHTuckUnitEigen
open RHPolynomialLpMap RHLegendreDirections
local notation "J" => toLp 1 (by norm_num : (0:ℝ) ≤ 1)
local notation "v" => directionPoly 1

theorem low_orth (n : ℕ) (q : Polynomial ℂ) (hq : q.degree < (n:ℕ)) :
    inner ℂ (J (v n)) (J q) = 0 := by
  have hs : q ∈ Submodule.span ℂ (v '' Set.Iio n) := by
    rw [RHTuckResidual.span_low (by norm_num : (0:ℝ)<1)]
    exact Polynomial.mem_degreeLT.mpr hq
  clear hq
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change i < n at hi
    have h := (orthonormal_iff_ite.mp
      (RHLegendreActual.directions_orthonormal (by norm_num : (0:ℝ)<1))) n i
    simpa [RHPolynomialLpMap.toLp_directionPoly, show n ≠ i by omega] using h
  | zero => simp
  | add x y hx hy ihx ihy => simp [map_add,inner_add_right,ihx,ihy]
  | smul a x hx ih => simp [map_smul,inner_smul_right,ih]

theorem eigen (n : ℕ) :
    RHTuckLinear.operator (v n) = (2*(harmonic n:ℂ)) • v n := by
  let r := RHTuckLinear.operator (v n) - (2*(harmonic n:ℂ)) • v n
  have hr : r.degree < (n:ℕ) := RHTuckResidual.residual_degree (v n) n
    (RHLegendreDirections.directionPoly_degree (by norm_num) n)
  have h1 := low_orth n r hr
  have h2 := low_orth n (RHTuckLinear.operator r) (RHTuckPreserves.low_degree hr)
  have hjr : J r = J (RHTuckLinear.operator (v n)) -
      (2*(harmonic n:ℂ)) • J (v n) := by simp [r]
  have hz : inner ℂ (J r) (J r) = 0 := by
    calc
      _ = inner ℂ (J (RHTuckLinear.operator (v n)) -
          (2*(harmonic n:ℂ)) • J (v n)) (J r) :=
        congrArg (fun z => inner ℂ z (J r)) hjr
      _ = inner ℂ (J (RHTuckLinear.operator (v n))) (J r) -
          conj (2*(harmonic n:ℂ)) * inner ℂ (J (v n)) (J r) := by
        rw [inner_sub_left,inner_smul_left]
      _ = 0 := by
        rw [← RHTuckLp.unit_hermitian (v n) r,h1,h2]
        simp
  have hj : J r = 0 := (inner_self_eq_zero).mp hz
  have hr0 : r = 0 := (RHTuckLp.toLp_injective (by norm_num : (0:ℝ)<1)) (by simpa using hj)
  exact sub_eq_zero.mp hr0

theorem integral_eigen (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    (∫ y in (-1:ℝ)..1, ((v n).eval (x:ℂ)-(v n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)) =
      (2*(harmonic n:ℂ)) * (v n).eval (x:ℂ) := by
  change (∫ y in (-1:ℝ)..1, RHTuckPolynomial.quotient (v n) x y) = _
  rw [RHTuckPolynomial.integral_eq_operator (v n) hx,eigen,Polynomial.eval_smul,smul_eq_mul]
end RHTuckUnitEigen
