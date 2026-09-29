import PrRed0511

/-! # 0511: `Pr` as a sum over the three prime shifts

`Pr n k = Σ_{m ∈ {2,3,4}} (Λ(m)/√m)·(1 + (−1)^{n+k})·Jm n k (log m)`, with
`Λ(2)/√2 = log2/√2`, `Λ(3)/√3 = log3/√3`, `Λ(4)/√4 = log2/2`. -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace RHPrSum0511
open RHConditionalLog5 RHLog5Bridge RHPrRed0511 RHLowBlock0494

local notation "Lw" => halfWidth

lemma term_int (n k : ℕ) (s : ℝ) : IntegrableOn (fun x => zp (basisPoly n) (x - s) * (basisPoly k).eval x)
    (Icc (-Lw) Lw) := by
  have hc : IntegrableOn (fun x => (basisPoly n).eval (x - s) * (basisPoly k).eval x) (Icc (-Lw) Lw) :=
    (by fun_prop : Continuous fun x => (basisPoly n).eval (x - s) * (basisPoly k).eval x).integrableOn_Icc
  have hi := hc.indicator (measurableSet_Icc (a := -Lw + s) (b := Lw + s))
  refine hi.congr_fun (fun x _ => ?_) measurableSet_Icc
  by_cases h : x ∈ Icc (-Lw + s) (Lw + s)
  · rw [indicator_of_mem h, zp_of_mem]; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · rw [indicator_of_notMem h, zp_of_not_mem, zero_mul]
    intro h'; exact h ⟨by linarith [h'.1], by linarith [h'.2]⟩

lemma term_int' (n k : ℕ) (s : ℝ) : IntegrableOn (fun x => zp (basisPoly n) (x + s) * (basisPoly k).eval x)
    (Icc (-Lw) Lw) := by
  have := term_int n k (-s); simpa [sub_neg_eq_add] using this

lemma lin3 {μ : Measure ℝ} {f2 g2 f3 g3 f4 g4 : ℝ → ℝ} (h2 : Integrable f2 μ) (k2 : Integrable g2 μ)
    (h3 : Integrable f3 μ) (k3 : Integrable g3 μ) (h4 : Integrable f4 μ) (k4 : Integrable g4 μ) (a b c : ℝ) :
    ∫ x, (a * (f2 x + g2 x) + b * (f3 x + g3 x) + c * (f4 x + g4 x)) ∂μ =
      a * ((∫ x, f2 x ∂μ) + ∫ x, g2 x ∂μ) + b * ((∫ x, f3 x ∂μ) + ∫ x, g3 x ∂μ) +
        c * ((∫ x, f4 x ∂μ) + ∫ x, g4 x ∂μ) := by
  have i2 := (h2.add k2).const_mul a
  have i3 := (h3.add k3).const_mul b
  have i4 := (h4.add k4).const_mul c
  rw [integral_add (f := fun x => a * (f2 x + g2 x) + b * (f3 x + g3 x)) (g := fun x => c * (f4 x + g4 x))
      (i2.add i3) i4,
    integral_add (f := fun x => a * (f2 x + g2 x)) (g := fun x => b * (f3 x + g3 x)) i2 i3,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add (f := f2) (g := g2) h2 k2, integral_add (f := f3) (g := g3) h3 k3,
    integral_add (f := f4) (g := g4) h4 k4]

noncomputable def w2 : ℝ := Real.log 2 / Real.sqrt 2
noncomputable def w3 : ℝ := Real.log 3 / Real.sqrt 3
noncomputable def w4 : ℝ := Real.log 2 / 2

theorem Pr_eq (n k : ℕ) :
    RHColDecomp0499.Pr n k = (1 + (-1) ^ (n + k)) *
      (w2 * Jm n k (Real.log 2) + w3 * Jm n k (Real.log 3) + w4 * Jm n k (Real.log 4)) := by
  have hL := halfWidth_pos
  have h5 : 2 * Lw = Real.log 5 := by unfold halfWidth; ring
  have hlog : ∀ m : ℝ, 1 ≤ m → m < 5 → 0 ≤ Real.log m ∧ Real.log m ≤ 2 * Lw := by
    intro m h1 h2; rw [h5]
    exact ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) h2.le⟩
  unfold RHColDecomp0499.Pr primeTerm
  have e : ∀ x, (∑ m ∈ range 5, ((ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m) *
      (zp (basisPoly n) (x - Real.log m) + zp (basisPoly n) (x + Real.log m))) * (basisPoly k).eval x =
      w2 * (zp (basisPoly n) (x - Real.log 2) * (basisPoly k).eval x + zp (basisPoly n) (x + Real.log 2) * (basisPoly k).eval x) +
      w3 * (zp (basisPoly n) (x - Real.log 3) * (basisPoly k).eval x + zp (basisPoly n) (x + Real.log 3) * (basisPoly k).eval x) +
      w4 * (zp (basisPoly n) (x - Real.log 4) * (basisPoly k).eval x + zp (basisPoly n) (x + Real.log 4) * (basisPoly k).eval x) := by
    intro x
    simp only [sum_range_succ, sum_range_zero]
    push_cast
    rw [RHStepA1G1.vm_zero, RHStepA1G1.vm_one, RHStepA1G1.vm_two, RHStepA1G1.vm_three, RHStepA1G1.vm_four,
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    unfold w2 w3 w4
    rw [show (2:ℝ) ^ 2 = 4 by norm_num]
    ring
  simp_rw [e]
  rw [lin3 (term_int n k _) (term_int' n k _) (term_int n k _) (term_int' n k _) (term_int n k _) (term_int' n k _)]
  have j2 := Jp_eq n k (hlog 2 (by norm_num) (by norm_num)).1 (hlog 2 (by norm_num) (by norm_num)).2
  have j3 := Jp_eq n k (hlog 3 (by norm_num) (by norm_num)).1 (hlog 3 (by norm_num) (by norm_num)).2
  have j4 := Jp_eq n k (hlog 4 (by norm_num) (by norm_num)).1 (hlog 4 (by norm_num) (by norm_num)).2
  unfold Jp Jm at j2 j3 j4
  unfold Jm
  rw [j2, j3, j4]
  ring

end RHPrSum0511

