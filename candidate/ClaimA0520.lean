import ApproxPolynomial0520
import SmoothIdentity0520
import KernelError0520
import PoleBounds0520

open MeasureTheory Set Polynomial
namespace RHClaimA0520
open RHLog5Bridge RHConditionalLog5 RHColDecomp0499 RHTruncation0520 RHApproxPolynomial0520

lemma g_error (n : ℕ) (hn : n ≤ 63) {x : ℝ} (hx : |x| < halfWidth) :
    |((1/2:ℝ)*((RH_Rebaseline.T_tail (halfWidth-x)+Real.log (halfWidth-x))+
      (RH_Rebaseline.T_tail (halfWidth+x)+Real.log (halfWidth+x))) -
      ((2*Real.log 2+Real.pi/2) - (gPoly false).eval x - (gPoly true).eval x)) *
      (basisPoly n).eval x| ≤ (9/10^18:ℝ) := by
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  have hminus := g64_approx (by linarith : 0 < halfWidth-x)
    (by rw [← RHRpErr0506.twoL]; linarith : halfWidth-x ≤ Real.log 5)
  have hplus := g64_approx (by linarith : 0 < halfWidth+x)
    (by rw [← RHRpErr0506.twoL]; linarith : halfWidth+x ≤ Real.log 5)
  have hb := RHBasisBound0520.basis_bound n hn hx.le
  rw [abs_mul]
  apply (mul_le_mul _ hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/10^18)).trans
    (by norm_num : (1/10^18:ℝ)*9 ≤ 9/10^18)
  rw [gPoly_eval,gPoly_eval]
  simp only [Bool.false_eq_true,if_false,if_true,← sub_eq_add_neg]
  have hh := abs_add_le
    (RH_Rebaseline.T_tail (halfWidth-x)+Real.log (halfWidth-x)+2*RHPolyL0500.ev g64 ((halfWidth-x)/2)-(2*Real.log 2+Real.pi/2))
    (RH_Rebaseline.T_tail (halfWidth+x)+Real.log (halfWidth+x)+2*RHPolyL0500.ev g64 ((halfWidth+x)/2)-(2*Real.log 2+Real.pi/2))
  have he : (1/2:ℝ)*((RH_Rebaseline.T_tail (halfWidth-x)+Real.log (halfWidth-x))+
      (RH_Rebaseline.T_tail (halfWidth+x)+Real.log (halfWidth+x))) -
      ((2*Real.log 2+Real.pi/2) - RHPolyL0500.ev g64 ((halfWidth-x)/2) - RHPolyL0500.ev g64 ((halfWidth+x)/2)) =
      (1/2:ℝ)*((RH_Rebaseline.T_tail (halfWidth-x)+Real.log (halfWidth-x)+2*RHPolyL0500.ev g64 ((halfWidth-x)/2)-(2*Real.log 2+Real.pi/2))+
      (RH_Rebaseline.T_tail (halfWidth+x)+Real.log (halfWidth+x)+2*RHPolyL0500.ev g64 ((halfWidth+x)/2)-(2*Real.log 2+Real.pi/2))) := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  linarith

lemma smooth_error (n : ℕ) (hn : n ≤ 63) {x : ℝ} (hx : |x| < halfWidth) :
    |RHSmoothIdentity0520.smooth n x - (approxPoly n).eval x| ≤ (1/10^14:ℝ) := by
  have hK := RHKernelError0520.kernel_error n hn hx.le
  rw [RHPolynKernel0520.kernel_eq q63 n (abs_le.mp hx.le)] at hK
  have hG := g_error n hn hx
  have hxhalf : |x/2| ≤ (1/2:ℝ) := by
    rw [abs_div,abs_two]
    linarith [RHPoleBounds0520.width_lt_one]
  have hh := RHHypApprox0520.hyp_error hxhalf
  have hC : |2*Cc n*(Real.cosh (x/2)-(RHHypApprox0520.hypPoly false).eval x)| ≤ (200/10^40:ℝ) := by
    rw [abs_mul,abs_mul,abs_two]
    have hc := RHPoleBounds0520.Cc_bound n hn
    have hc' : 2*|Cc n| ≤ 200 := by linarith
    have hm := mul_le_mul hc' hh.1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 200)
    convert hm using 1 <;> ring
  have hS : |2*Ss n*(Real.sinh (x/2)-(RHHypApprox0520.hypPoly true).eval x)| ≤ (200/10^40:ℝ) := by
    rw [abs_mul,abs_mul,abs_two]
    have hs := RHPoleBounds0520.Ss_bound n hn
    have hs' : 2*|Ss n| ≤ 200 := by linarith
    have hm := mul_le_mul hs' hh.2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 200)
    convert hm using 1 <;> ring
  let a : ℝ := (1/2:ℝ)*(∫ y in Icc (-halfWidth) halfWidth, Rk |x-y| *((basisPoly n).eval x-(basisPoly n).eval y)) - (RHPolynKernel0520.kernelPoly q63 n).eval x
  let b : ℝ := ((1/2:ℝ)*((RH_Rebaseline.T_tail (halfWidth-x)+Real.log (halfWidth-x))+
      (RH_Rebaseline.T_tail (halfWidth+x)+Real.log (halfWidth+x))) -
      ((2*Real.log 2+Real.pi/2)-(gPoly false).eval x-(gPoly true).eval x))*(basisPoly n).eval x
  let c : ℝ := 2*Cc n*(Real.cosh (x/2)-(RHHypApprox0520.hypPoly false).eval x)
  let d : ℝ := 2*Ss n*(Real.sinh (x/2)-(RHHypApprox0520.hypPoly true).eval x)
  have he : RHSmoothIdentity0520.smooth n x - (approxPoly n).eval x = a+b+c-d := by
    simp only [RHSmoothIdentity0520.smooth,approxPoly,eval_add,eval_sub,eval_mul,eval_C]
    dsimp [a,b,c,d]
    ring
  rw [he]
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a+b) c
  have h3 := abs_sub (a+b+c) d
  change |a| ≤ _ at hK
  change |b| ≤ _ at hG
  change |c| ≤ _ at hC
  change |d| ≤ _ at hS
  have hw := RHPoleBounds0520.width_lt_one
  linarith

theorem claimA : RHInterface0516.ClaimA (1/10^14:ℝ) := by
  intro o i
  have hn : RHConditionalLog5.degree o i ≤ 63 := by
    have hi := i.isLt
    unfold RHConditionalLog5.degree
    split <;> omega
  refine ⟨approxPoly (RHConditionalLog5.degree o i), approxPoly_degree _ hn, ?_⟩
  filter_upwards [RHSmoothIdentity0520.column_add_Sx_ae (RHConditionalLog5.degree o i)] with x h hx
  change |RHWeilColumnCandidate.column halfWidth (basisPoly (RHConditionalLog5.degree o i)) x +
    RHInterface0516.Sx (RHConditionalLog5.degree o i) x - (approxPoly (RHConditionalLog5.degree o i)).eval x| ≤ _
  rw [h hx]
  exact smooth_error _ hn hx

end RHClaimA0520
