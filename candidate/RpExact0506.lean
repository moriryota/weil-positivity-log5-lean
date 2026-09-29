import AlgoBall0505
import RkApprox0500

/-! # 0506: exact polynomial part of `Rp` in Legendre form

`Qs s = Q(s/2)` (0500). `RpQ n k = ∫_I ½ (∫_I Qs|x−y| (b_n x − b_n y)) b_k x` equals
`L² c_n c_k/(2k+1) · γ n J rt k` with `rt j = q_j (L/2)^j`, `c_n = √((2n+1)/(2L))`, `J = 81`.
 -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace RHRpExact0506
open RHConditionalLog5 RHLog5Bridge RHLeg0503 RHGForm0505

noncomputable def Qs (s : ℝ) : ℝ := RHPolyL0500.ev RHRkApprox0500.ql (s / 2)
noncomputable def cc (n : ℕ) : ℝ := Real.sqrt ((2 * n + 1) / (2 * halfWidth))
noncomputable def rt (j : ℕ) : ℝ := ((RHRkApprox0500.ql.getD j 0 : ℚ) : ℝ) * (halfWidth / 2) ^ j
def J : ℕ := RHRkApprox0500.ql.length

noncomputable def RpQ (n k : ℕ) : ℝ := ∫ x in Icc (-halfWidth) halfWidth,
  (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) *
    (basisPoly k).eval x

lemma ev_eq_sum : ∀ (p : List ℚ) (t : ℝ),
    RHPolyL0500.ev p t = ∑ i ∈ range p.length, ((p.getD i 0 : ℚ) : ℝ) * t ^ i
  | [], t => by simp [RHPolyL0500.ev]
  | c :: p, t => by
      rw [RHPolyL0500.ev, ev_eq_sum p t, List.length_cons, sum_range_succ', mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]; congr 1; exact sum_congr rfl (fun i _ => by ring)

lemma Qs_scale (u v : ℝ) : Qs |halfWidth * u - halfWidth * v| = ∑ j ∈ range J, rt j * |u - v| ^ j := by
  have hL := halfWidth_pos
  unfold Qs rt J
  rw [ev_eq_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_pos hL]
  ring

lemma set_scale (F : ℝ → ℝ) :
    ∫ x in Icc (-halfWidth) halfWidth, F x = halfWidth * ∫ u in (-1:ℝ)..1, F (halfWidth * u) := by
  have hL := halfWidth_pos
  rw [RHEntry00_0495.setI, intervalIntegral.integral_comp_mul_left F hL.ne', smul_eq_mul, mul_neg, mul_one]
  field_simp

lemma bscale (n : ℕ) (u : ℝ) : (basisPoly n).eval (halfWidth * u) = cc n * p n u := by
  rw [RHLink0505.basisPoly_eval]; unfold cc
  congr 2; field_simp [halfWidth_pos.ne']

theorem RpQ_eq (n k : ℕ) :
    RpQ n k = halfWidth ^ 2 * cc n * cc k / (2 * k + 1) * γ n J rt k := by
  have hL := halfWidth_pos
  have inner : ∀ u : ℝ, (∫ y in Icc (-halfWidth) halfWidth,
      Qs |halfWidth * u - y| * ((basisPoly n).eval (halfWidth * u) - (basisPoly n).eval y)) =
      halfWidth * cc n * ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, rt j * |u - v| ^ j) * (p n u - p n v) := by
    intro u
    rw [set_scale (fun y => Qs |halfWidth * u - y| * ((basisPoly n).eval (halfWidth * u) - (basisPoly n).eval y))]
    simp only [Qs_scale, bscale]
    rw [mul_assoc]; congr 1
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext v; ring
  unfold RpQ
  rw [set_scale (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
    Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x)]
  simp only [inner]; simp only [bscale]
  have e := entry_eq n J k rt
  have h2 : (∫ u in (-1:ℝ)..1, (1/2:ℝ) * (halfWidth * cc n *
      ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, rt j * |u - v| ^ j) * (p n u - p n v)) * (cc k * p k u)) =
      (1/2) * halfWidth * cc n * cc k * ∫ u in (-1:ℝ)..1, p k u *
        ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, rt j * |u - v| ^ j) * (p n u - p n v) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring
  rw [h2, e]
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

end RHRpExact0506

