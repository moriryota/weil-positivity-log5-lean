import RpExact0506

open Polynomial MeasureTheory Set Finset
open scoped BigOperators

namespace RHPolynKernel0520
open RHConditionalLog5 RHLog5Bridge RHLeg0503 RHLegVec0503 RHGForm0505 RHRpExact0506

lemma leg_natDegree : ∀ n : ℕ, (leg n).natDegree ≤ n
  | 0 => by simp [leg]
  | 1 => by simp [leg]
  | n + 2 => by
      rw [leg]
      apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · have h := natDegree_mul_le (p := C (2 * (n : ℝ) + 3) * X) (q := leg (n + 1))
        have hX : (C (2 * (n : ℝ) + 3) * X).natDegree ≤ 1 :=
          (natDegree_C_mul_le _ _).trans natDegree_X_le
        have hi := leg_natDegree (n + 1)
        omega
      · exact (natDegree_C_mul_le _ _).trans ((leg_natDegree n).trans (by omega))

noncomputable def vecPoly (N : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ l ∈ range N, C (c l) * leg l

lemma vecPoly_eval (N : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    (vecPoly N c).eval u = evV N c u := by
  simp [vecPoly, evV, p, Polynomial.eval_finsetSum]

lemma vecPoly_degree (N d : ℕ) (c : ℕ → ℝ) (hN : N ≤ d + 1) :
    (vecPoly N c).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro l hl
  exact (natDegree_C_mul_le _ _).trans ((leg_natDegree l).trans (by simp at hl; omega))

noncomputable def scaledCoeffs (v : List ℚ) (j : ℕ) : ℝ :=
  (v.getD j 0 : ℝ) * (halfWidth / 2) ^ j

noncomputable def kernelPoly (v : List ℚ) (n : ℕ) : Polynomial ℝ :=
  C ((1/2:ℝ) * halfWidth * cc n) *
    (vecPoly (n + 1 + v.length) (γ n v.length (scaledCoeffs v))).comp
      (C halfWidth⁻¹ * X)

lemma kernelPoly_degree (v : List ℚ) (n : ℕ) (hv : v.length ≤ 64) (hn : n ≤ 63) :
    (kernelPoly v n).natDegree ≤ 127 := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have h1 := vecPoly_degree (n + 1 + v.length) 127 (γ n v.length (scaledCoeffs v)) (by omega)
  have h2 : (C halfWidth⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  exact (Nat.mul_le_mul h1 h2).trans (by norm_num)

lemma kernel_scale (v : List ℚ) (u w : ℝ) :
    RHPolyL0500.ev v (|halfWidth * u - halfWidth * w| / 2) =
      ∑ j ∈ range v.length, scaledCoeffs v j * |u - w| ^ j := by
  rw [ev_eq_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_pos halfWidth_pos]
  unfold scaledCoeffs
  ring

lemma kernelPoly_eval_scaled (v : List ℚ) (n : ℕ) (u : ℝ) :
    (kernelPoly v n).eval (halfWidth * u) =
      (1/2:ℝ) * halfWidth * cc n *
        evV (n + 1 + v.length) (γ n v.length (scaledCoeffs v)) u := by
  simp only [kernelPoly, eval_mul, eval_C, eval_comp, eval_X]
  have he : halfWidth⁻¹ * (halfWidth * u) = u := by field_simp [halfWidth_pos.ne']
  rw [he, vecPoly_eval]

lemma kernel_eq (v : List ℚ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-halfWidth) halfWidth) :
    (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
      RHPolyL0500.ev v (|x-y| / 2) * ((basisPoly n).eval x - (basisPoly n).eval y)) =
      (kernelPoly v n).eval x := by
  have hL := halfWidth_pos
  have hu : x / halfWidth ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hL).mpr; simpa using hx.1
    · apply (div_le_iff₀ hL).mpr; simpa using hx.2
  have hscale : halfWidth * (x / halfWidth) = x := by field_simp [halfWidth_pos.ne']
  conv_lhs => rw [← hscale]
  rw [set_scale]
  simp only [kernel_scale, bscale]
  have he : (∫ w in (-1:ℝ)..1,
      (∑ j ∈ range v.length, scaledCoeffs v j * |x / halfWidth - w| ^ j) *
      (cc n * p n (x / halfWidth) - cc n * p n w)) =
      cc n * ∫ w in (-1:ℝ)..1,
      (∑ j ∈ range v.length, scaledCoeffs v j * |x / halfWidth - w| ^ j) *
      (p n (x / halfWidth) - p n w) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext w; ring
  rw [he, G_eq n v.length (scaledCoeffs v) hu]
  have hk := kernelPoly_eval_scaled v n (x / halfWidth)
  rw [hscale] at hk
  rw [hk]
  ring

theorem exists_kernel_polynomial (v : List ℚ) (n : ℕ)
    (hv : v.length ≤ 64) (hn : n ≤ 63) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 127 ∧ ∀ x ∈ Icc (-halfWidth) halfWidth,
      (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
        RHPolyL0500.ev v (|x-y| / 2) * ((basisPoly n).eval x - (basisPoly n).eval y)) = P.eval x :=
  ⟨kernelPoly v n, kernelPoly_degree v n hv hn, fun _ hx => kernel_eq v n hx⟩

end RHPolynKernel0520

