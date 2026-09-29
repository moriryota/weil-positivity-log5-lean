import PolynKernel0520
import HypApprox0520
import Truncation0520

open Polynomial
namespace RHApproxPolynomial0520
open RHLowBlock0494 RHLog5Bridge RHConditionalLog5 RHColDecomp0499 RHTruncation0520 RHPolynKernel0520

noncomputable def listPoly : List ℚ → Polynomial ℝ
  | [] => 0
  | c::v => C (c:ℝ) + X * listPoly v

lemma listPoly_eval (v : List ℚ) (x : ℝ) : (listPoly v).eval x = RHPolyL0500.ev v x := by
  induction v with
  | nil => simp [listPoly,RHPolyL0500.ev]
  | cons c v ih => simp [listPoly,RHPolyL0500.ev,ih]

lemma listPoly_degree : ∀ v : List ℚ, (listPoly v).natDegree ≤ v.length-1
  | [] => by simp [listPoly]
  | [c] => by simp [listPoly]
  | c::d::v => by
      have hi := listPoly_degree (d::v)
      simp only [listPoly]
      apply (natDegree_add_le _ _).trans
      apply max_le
      · simp
      · have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := listPoly (d::v))
        simp only [natDegree_X, List.length_cons] at *
        change (X * listPoly (d::v)).natDegree ≤ (v.length+1+1)-1
        omega

lemma basis_degree (n : ℕ) : (basisPoly n).natDegree ≤ n := by
  have he : basisPoly n = C (RHRpExact0506.cc n) *
      (RHLeg0503.leg n).comp (C halfWidth⁻¹ * X) := by
    apply Polynomial.funext
    intro x
    rw [RHLink0505.basisPoly_eval]
    simp only [eval_mul,eval_C,eval_comp,eval_X]
    unfold RHRpExact0506.cc RHLeg0503.p
    simp [div_eq_mul_inv, mul_comm]
  rw [he]
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have h1 := leg_natDegree n
  have h2 : (C halfWidth⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  simpa using Nat.mul_le_mul h1 h2

noncomputable def gPoly (plus : Bool) : Polynomial ℝ :=
  (listPoly g64).comp (C (halfWidth/2) + C (if plus then (1/2:ℝ) else -(1/2:ℝ))*X)

lemma gPoly_eval (plus : Bool) (x : ℝ) :
    (gPoly plus).eval x = RHPolyL0500.ev g64 ((halfWidth + (if plus then x else -x))/2) := by
  simp only [gPoly,eval_comp,eval_add,eval_C,eval_mul,eval_X,listPoly_eval]
  congr 1
  cases plus <;> simp <;> ring

lemma gPoly_degree (plus : Bool) : (gPoly plus).natDegree ≤ 64 := by
  apply natDegree_comp_le.trans
  have h1 : (listPoly g64).natDegree ≤ 64 := (listPoly_degree g64).trans (by decide +kernel)
  have h2 : (C (halfWidth/2) + C (if plus then (1/2:ℝ) else -(1/2:ℝ))*X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  simpa using Nat.mul_le_mul h1 h2

noncomputable def approxPoly (n : ℕ) : Polynomial ℝ :=
  C (h0c + (harmonic n : ℝ) - Real.log halfWidth + (2*Real.log 2+Real.pi/2))*basisPoly n +
  kernelPoly q63 n - (gPoly false + gPoly true)*basisPoly n +
  C (2*Cc n)*RHHypApprox0520.hypPoly false - C (2*Ss n)*RHHypApprox0520.hypPoly true

lemma approxPoly_degree (n : ℕ) (hn : n ≤ 63) : (approxPoly n).natDegree ≤ 127 := by
  have hb := basis_degree n
  have hg : ((gPoly false + gPoly true)*basisPoly n).natDegree ≤ 127 := by
    have hsum := natDegree_add_le (gPoly false) (gPoly true)
    have hgg : (gPoly false + gPoly true).natDegree ≤ 64 :=
      hsum.trans (max_le (gPoly_degree false) (gPoly_degree true))
    have hm := natDegree_mul_le (p := gPoly false + gPoly true) (q := basisPoly n)
    omega
  have h0 : (C (h0c + (harmonic n : ℝ) - Real.log halfWidth + (2*Real.log 2+Real.pi/2))*basisPoly n).natDegree ≤ 127 :=
    (natDegree_C_mul_le _ _).trans (hb.trans (by omega))
  have hk := kernelPoly_degree q63 n (by decide +kernel) hn
  have hc : (C (2*Cc n)*RHHypApprox0520.hypPoly false).natDegree ≤ 127 :=
    (natDegree_C_mul_le _ _).trans ((RHHypApprox0520.hypPoly_degree false).trans (by omega))
  have hs : (C (2*Ss n)*RHHypApprox0520.hypPoly true).natDegree ≤ 127 :=
    (natDegree_C_mul_le _ _).trans ((RHHypApprox0520.hypPoly_degree true).trans (by omega))
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le h0 hk)) hg)) hc)) hs)

end RHApproxPolynomial0520
