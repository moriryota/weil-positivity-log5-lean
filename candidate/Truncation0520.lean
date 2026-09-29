import RkApprox0500
import GApprox0501

namespace RHTruncation0520
open RHPolyL0500 RHRkApprox0500 RHGApprox0501

def q63 : List ℚ := ql.take 64
def g64 : List ℚ := (integL ql).take 65

lemma ev_take_error (v : List ℚ) (N : ℕ) (hN : N ≤ v.length) {t : ℝ}
    (ht : 0 ≤ t) (hta : t ≤ (aQ:ℝ)) :
    |ev v t - ev (v.take N) t| ≤
      ((aQ^N * evQ (absL (v.drop N)) aQ : ℚ):ℝ) := by
  have he : ev v t = ev (v.take N) t + t^N * ev (v.drop N) t := by
    conv_lhs => rw [← List.take_append_drop N v, ev_append]
    rw [List.length_take, Nat.min_eq_left hN]
  rw [he, add_sub_cancel_left, abs_mul, abs_of_nonneg (pow_nonneg ht N)]
  have hpow : t^N ≤ (aQ:ℝ)^N := pow_le_pow_left₀ ht hta N
  have hval := abs_ev_le_evQ (v.drop N) aQ ht hta
  have hnon : 0 ≤ ((evQ (absL (v.drop N)) aQ : ℚ):ℝ) := (abs_nonneg _).trans hval
  push_cast
  exact mul_le_mul hpow hval (abs_nonneg _) (pow_nonneg (le_trans ht hta) N)

lemma r_tail_check : aQ^64 * evQ (absL (ql.drop 64)) aQ ≤ (3/10^19 : ℚ) := by decide +kernel
lemma g_tail_check : 2 * aQ^65 * evQ (absL ((integL ql).drop 65)) aQ ≤ (6/10^21 : ℚ) := by decide +kernel

lemma q63_error {t : ℝ} (ht : 0 ≤ t) (hta : t ≤ (aQ:ℝ)) :
    |ev ql t - ev q63 t| ≤ (3/10^19:ℝ) := by
  have h := ev_take_error ql 64 (by decide +kernel) ht hta
  have hc := (Rat.cast_le (K := ℝ)).mpr r_tail_check
  push_cast at hc h
  exact h.trans hc

lemma g64_error {t : ℝ} (ht : 0 ≤ t) (hta : t ≤ (aQ:ℝ)) :
    |2*ev (integL ql) t - 2*ev g64 t| ≤ (6/10^21:ℝ) := by
  have h := ev_take_error (integL ql) 65 (by decide +kernel) ht hta
  change |ev (integL ql) t - ev g64 t| ≤ _ at h
  have hc := (Rat.cast_le (K := ℝ)).mpr g_tail_check
  push_cast at hc h
  rw [← mul_sub, abs_mul]; norm_num
  linarith

lemma half_arg_le {s : ℝ} (hs : s ≤ Real.log 5) : s/2 ≤ (aQ:ℝ) := by
  have h5 := RHEntry00Bounds0495.b_l5.2
  have hq : (RHEntry00Bounds0495.l5H : ℝ) ≤ 2*(aQ:ℝ) := by
    have h : RHEntry00Bounds0495.l5H ≤ 2*aQ := by decide +kernel
    exact_mod_cast h
  linarith

theorem rk63_approx {s : ℝ} (hs : 0 < s) (hs5 : s ≤ Real.log 5) :
    |RHColDecomp0499.Rk s - ev q63 (s/2)| ≤ (1/10^18:ℝ) := by
  have h1 := Rk_approx hs hs5
  have h2 := q63_error (by positivity : 0 ≤ s/2) (half_arg_le hs5)
  have h := abs_sub_le (RHColDecomp0499.Rk s) (ev ql (s/2)) (ev q63 (s/2))
  linarith

theorem g64_approx {s : ℝ} (hs : 0 < s) (hs5 : s ≤ Real.log 5) :
    |RH_Rebaseline.T_tail s + Real.log s + 2*ev g64 (s/2) - (2*Real.log 2 + Real.pi/2)| ≤ (1/10^18:ℝ) := by
  have h1 := g_approx hs hs5
  have h2 := g64_error (by positivity : 0 ≤ s/2) (half_arg_le hs5)
  have harg := half_arg_le hs5
  have hs2 : s ≤ 2 := by norm_num [aQ] at harg; linarith
  have h3 := abs_add_le (RH_Rebaseline.T_tail s + Real.log s + Gq s - (2*Real.log 2 + Real.pi/2))
    (2*ev g64 (s/2) - Gq s)
  have he : |2*ev g64 (s/2) - Gq s| = |2*ev (integL ql) (s/2) - 2*ev g64 (s/2)| := by
    unfold Gq; exact abs_sub_comm _ _
  rw [he] at h3
  have he2 : RH_Rebaseline.T_tail s + Real.log s + Gq s - (2*Real.log 2 + Real.pi/2) +
      (2*ev g64 (s/2) - Gq s) =
      RH_Rebaseline.T_tail s + Real.log s + 2*ev g64 (s/2) - (2*Real.log 2 + Real.pi/2) := by ring
  rw [he2] at h3
  nlinarith

end RHTruncation0520

