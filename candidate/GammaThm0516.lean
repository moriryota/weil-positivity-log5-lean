import GammaFull0516

/-! # 0516: `γ_ik = ∫_{−1}^1 φ_i φ_k` in terms of `N, K, F, OO, X`

`γ = ¼((1+e) N_ik + 2 K_ik) + ½ Σ_a W_a (1+e)(F i k s_a + F k i s_a)
     + Σ_{a,b} W_a W_b (1+e) OO i k s_a s_b + W_0² (X i k s_0 s_0 + X k i s_0 s_0)`,
`e = (−1)^{i+k}`, `s_a = Sh a = σ_{2,3,4}`, `W = (w2, w3, w4)`. -/

open Set MeasureTheory intervalIntegral Finset

namespace RHGammaThm0516
open RHLeg0503 RHSingDef0516 RHPairInt0516 RHGammaExp0516 RHGammaFull0516

noncomputable def A (n : ℕ) (u : ℝ) : ℝ := (1 / 2) * lg u * p n u

lemma phi_eq (n : ℕ) (u : ℝ) : phi n u = A n u + pr n u := rfl

lemma lgsq_ii (i k : ℕ) : IntervalIntegrable (fun u => lg u ^ 2 * (p i u * p k u)) volume (-1) 1 := by
  have hc : Continuous fun u => p i u * p k u := (continuous_p i).mul (continuous_p k)
  have i1 := RHNu0514.log2_ii.mul_continuousOn hc.continuousOn
  have i2 := (RHBaseNK0515.kw_ii.mul_continuousOn hc.continuousOn).const_mul 2
  have i3 := log1m_sq_ii.mul_continuousOn hc.continuousOn
  refine ((i1.add i2).add i3).congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ?_)
  filter_upwards [lg_ae] with u hu hu'
  show _ = lg u ^ 2 * (p i u * p k u)
  rw [hu hu']; ring

lemma AA_ii (i k : ℕ) : IntervalIntegrable (fun u => A i u * A k u) volume (-1) 1 :=
  ((lgsq_ii i k).const_mul (1 / 4)).congr (fun u _ => by simp only [A]; ring)

theorem AA (i k : ℕ) : ∫ u in (-1:ℝ)..1, A i u * A k u =
    (1 / 4) * ((1 + (-1) ^ (i + k)) * RHRec2D0515.Mw (fun x => Real.log (1 + x) ^ 2) i k +
      2 * RHRec2D0515.Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k) := by
  rw [← lgsq, ← intervalIntegral.integral_const_mul]
  congr 1; funext u; simp only [A]; ring

lemma Apr_term_ii (i k : ℕ) (a : Fin 3) :
    IntervalIntegrable (fun u => W a * ((1 / 2) * (lg u * p i u * pm k (Sh a) u) +
      (1 / 2) * (lg u * p i u * pp k (Sh a) u))) volume (-1) 1 := by
  obtain ⟨h1, h2⟩ := ii_lg_pieces i k (Sh a)
  exact ((h1.const_mul _).add (h2.const_mul _)).const_mul _

theorem Apr (i k : ℕ) : ∫ u in (-1:ℝ)..1, A i u * pr k u =
    (1 / 2) * ∑ a : Fin 3, W a * ((1 + (-1) ^ (i + k)) * F i k (Sh a)) := by
  have e : (fun u => A i u * pr k u) = fun u => ∑ a : Fin 3, W a * ((1 / 2) * (lg u * p i u * pm k (Sh a) u) +
      (1 / 2) * (lg u * p i u * pp k (Sh a) u)) := by
    funext u; rw [pr_sum, mul_sum]; refine sum_congr rfl (fun a _ => ?_); simp only [A]; ring
  rw [e, intervalIntegral.integral_finsetSum (fun a _ => Apr_term_ii i k a), mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  obtain ⟨h1, h2⟩ := ii_lg_pieces i k (Sh a)
  obtain ⟨b0, b2⟩ := Sh_bounds a
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (h1.const_mul _) (h2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, P5 i k b0 b2, P6 i k b0 b2]
  ring

lemma Apr_ii (i k : ℕ) : IntervalIntegrable (fun u => A i u * pr k u) volume (-1) 1 := by
  have := IntervalIntegrable.sum (Finset.univ) (fun a _ => Apr_term_ii i k a)
  refine this.congr (fun u _ => ?_)
  simp only [Finset.sum_apply]
  rw [pr_sum, mul_sum]; refine sum_congr rfl (fun a _ => ?_); simp only [A]; ring

theorem prA (i k : ℕ) : ∫ u in (-1:ℝ)..1, pr i u * A k u =
    (1 / 2) * ∑ a : Fin 3, W a * ((1 + (-1) ^ (i + k)) * F k i (Sh a)) := by
  rw [show (fun u => pr i u * A k u) = fun u => A k u * pr i u by funext u; ring, Apr, add_comm k i]

lemma prA_ii (i k : ℕ) : IntervalIntegrable (fun u => pr i u * A k u) volume (-1) 1 :=
  (Apr_ii k i).congr (fun u _ => by ring)

lemma prpr_ii (i k : ℕ) : IntervalIntegrable (fun u => pr i u * pr k u) volume (-1) 1 := by
  have := IntervalIntegrable.sum (Finset.univ) (fun a _ =>
    IntervalIntegrable.sum (Finset.univ) (fun b _ => ii_pr_pr i k a b))
  refine this.congr (fun u _ => ?_)
  simp only [Finset.sum_apply]
  rw [pr_sum, pr_sum, sum_mul_sum]

/-- The value of one `(a, b)` block of `prpr`. -/
lemma block (i k : ℕ) (a b : Fin 3) :
    (∫ u in (-1:ℝ)..1, pm i (Sh a) u * pm k (Sh b) u) + (∫ u in (-1:ℝ)..1, pm i (Sh a) u * pp k (Sh b) u) +
      (∫ u in (-1:ℝ)..1, pp i (Sh a) u * pm k (Sh b) u) + (∫ u in (-1:ℝ)..1, pp i (Sh a) u * pp k (Sh b) u) =
    (1 + (-1) ^ (i + k)) * OO i k (Sh a) (Sh b) +
      (if a = 0 ∧ b = 0 then X i k (Sh a) (Sh b) + X k i (Sh b) (Sh a) else 0) := by
  obtain ⟨a0, a2⟩ := Sh_bounds a
  obtain ⟨b0, b2⟩ := Sh_bounds b
  rw [P1 i k a0 a2 b0 b2, P2 i k a0 a2 b0 b2]
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    have h : Sh 0 + Sh 0 ≤ 2 := by simp only [Sh]; exact sig_sum_le (by norm_num) (by norm_num) (by norm_num)
    rw [P3 i k a0 b0 h, P4 i k a0 b0 h, if_pos ⟨rfl, rfl⟩]; ring
  · have h : 2 ≤ Sh a + Sh b := by
      fin_cases a <;> fin_cases b <;> simp only [Sh] at hab ⊢ <;>
        first
        | exact absurd ⟨rfl, rfl⟩ hab
        | exact sig_sum_ge (by norm_num) (by norm_num) (by norm_num)
    rw [P3z i k h, P4z i k h, if_neg hab]; ring

theorem gamma_eq (i k : ℕ) : ∫ u in (-1:ℝ)..1, phi i u * phi k u =
    (1 / 4) * ((1 + (-1) ^ (i + k)) * RHRec2D0515.Mw (fun x => Real.log (1 + x) ^ 2) i k +
      2 * RHRec2D0515.Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k) +
    (1 / 2) * ∑ a : Fin 3, W a * ((1 + (-1) ^ (i + k)) * (F i k (Sh a) + F k i (Sh a))) +
    ∑ a : Fin 3, ∑ b : Fin 3, W a * W b * ((1 + (-1) ^ (i + k)) * OO i k (Sh a) (Sh b)) +
    W 0 * W 0 * (X i k (Sh 0) (Sh 0) + X k i (Sh 0) (Sh 0)) := by
  have e : (fun u => phi i u * phi k u) =
      fun u => A i u * A k u + A i u * pr k u + pr i u * A k u + pr i u * pr k u := by
    funext u; rw [phi_eq, phi_eq]; ring
  rw [e, intervalIntegral.integral_add (((AA_ii i k).add (Apr_ii i k)).add (prA_ii i k)) (prpr_ii i k),
    intervalIntegral.integral_add ((AA_ii i k).add (Apr_ii i k)) (prA_ii i k),
    intervalIntegral.integral_add (AA_ii i k) (Apr_ii i k), AA, Apr, prA, prpr]
  simp only [block]
  simp only [Fin.sum_univ_three, Fin.isValue]
  simp
  ring

end RHGammaThm0516

