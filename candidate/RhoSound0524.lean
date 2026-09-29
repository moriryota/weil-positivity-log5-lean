import GamSound0523
import Rho0522
import SxScale0516
import Interface0524
import EntryRepr0512
import PolyExp0522

/-! # 0524: from the kernel-checked ρ tables to `NumBound (1/10^14) (1/10^4) (99/100)`. -/

open Finset MeasureTheory
open scoped BigOperators

namespace RHRhoSound0524
open RHBall0504 RHBallVec0504 RHBallDot0509 RHBallMisc0512 RHG6Core0522 RHRec2D0515 RHGam0522 RHRho0522
  RHConditionalLog5 RHEntryBall0512 RHLog5Bridge

local notation "S" => (2:ℕ) ^ 256

lemma hS : 0 < S := by positivity

noncomputable def sh (n : ℕ) : ℝ := Real.sqrt ((2 * n + 1) / 2)

lemma sh_sq (n : ℕ) : sh n ^ 2 = (2 * n + 1) / 2 := Real.sq_sqrt (by positivity)

/-! ### √ balls -/

lemma sq_mem (n : ℕ) (hn : n < 64) : mem S (sh n) (gz sqL n) := by
  have h := (List.all_eq_true.mp sq_ok) n (List.mem_range.mpr hn)
  simp only [sqOK, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  set b := gz sqL n
  have hS' : (0:ℝ) < S := by positivity
  have r0 : (0:ℝ) ≤ ((b.1 : ℝ) - b.2) / S := div_nonneg (by exact_mod_cast h0) hS'.le
  have r1 : (((b.1 : ℝ) - b.2) / S) ^ 2 ≤ (2 * n + 1) / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (((b.1 - b.2) ^ 2 * 2 : ℤ) : ℝ) ≤ (((2 * (n : ℤ) + 1) * (2 ^ 256) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; norm_num at this ⊢; nlinarith
  have r2 : (2 * (n:ℝ) + 1) / 2 ≤ (((b.1 : ℝ) + b.2) / S) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (((2 * (n : ℤ) + 1) * (2 ^ 256) ^ 2 : ℤ) : ℝ) ≤ (((b.1 + b.2) ^ 2 * 2 : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; norm_num at this ⊢; nlinarith
  have r3 : (0:ℝ) ≤ ((b.1 : ℝ) + b.2) / S := by
    apply div_nonneg _ hS'.le
    have : (0:ℝ) ≤ (b.1 : ℝ) - b.2 := by exact_mod_cast h0
    have : (0:ℝ) ≤ (b.2 : ℝ) := by positivity
    linarith
  obtain ⟨l1, l2⟩ := sqrt_bounds r0 r1 r2 r3
  change ((b.1 : ℝ) - b.2) / S ≤ sh n at l1
  change sh n ≤ ((b.1 : ℝ) + b.2) / S at l2
  have key : mem S (sh n) (b.1, b.2) := by
    apply mem_of_bounds' hS
    · rw [sub_div] at l1; norm_num at l1 ⊢; linarith
    · rw [add_div] at l2; norm_num at l2 ⊢; linarith
  simpa using key

/-! ### T and σ balls -/

lemma rescale {x : ℝ} {c : ℤ} {r : ℕ} (h : mem (2 ^ 128) x (c, r)) :
    mem S x (c * 2 ^ 128, r * 2 ^ 128) := by
  unfold mem at *
  simp only at h ⊢
  have e1 : ((c * 2 ^ 128 : ℤ) : ℝ) / ((2 ^ 256 : ℕ) : ℝ) = (c : ℝ) / ((2 ^ 128 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  have e2 : ((r * 2 ^ 128 : ℕ) : ℝ) / ((2 ^ 256 : ℕ) : ℝ) = (r : ℝ) / ((2 ^ 128 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e1, e2]; exact h

lemma Tb_mem (i k : ℕ) (hi : i < 64) (hk : k < 128) : mem S (RHPrEncl0511.T i k) (Tb i k) := by
  have h := RHPrAll0512.pr_all i k hi hk
  unfold Tb
  exact rescale h

lemma Mp_len : ∀ j < 64, 128 ≤ (RHMpTab0515.tab.getD j []).length := by
  have h : (List.range 64).all (fun j => decide (128 ≤ (RHMpTab0515.tab.getD j []).length)) = true := by decide +kernel
  intro j hj; simpa [hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

noncomputable def sig (i k : ℕ) : ℝ := Mw (fun t => Real.log (1 + t)) i k + 2 * RHPrEncl0511.T i k

lemma sig_mem (i k : ℕ) (hi : i < 64) (hk : k < 128) : mem S (sig i k) (sigB i k) := by
  have h1 : mem S (Mw (fun t => Real.log (1 + t)) i k) (gzz RHMpTab0515.tab i k) :=
    RHMpTab0515.Mp_mem i k (by have := Mp_len i hi; omega)
  have h2 := mem_smul hS 2 (d := 1) (by norm_num) (Tb_mem i k hi hk)
  have := mem_add h1 h2
  unfold sig sigB; convert this using 1; push_cast; ring

/-! ### identification of `Gam` and `sco` -/

lemma cc_eq (n : ℕ) : RHRpExact0506.cc n * Real.sqrt halfWidth = sh n := by
  unfold RHRpExact0506.cc sh
  have hL := halfWidth_pos
  rw [← Real.sqrt_mul (div_nonneg (by positivity) (by linarith))]
  congr 1; field_simp

lemma Lcc (a b : ℕ) : halfWidth * (RHRpExact0506.cc a * RHRpExact0506.cc b) = sh a * sh b := by
  rw [← cc_eq, ← cc_eq]
  have h := Real.mul_self_sqrt halfWidth_pos.le
  calc halfWidth * (RHRpExact0506.cc a * RHRpExact0506.cc b)
      = RHRpExact0506.cc a * RHRpExact0506.cc b * (Real.sqrt halfWidth * Real.sqrt halfWidth) := by rw [h]; ring
    _ = _ := by ring

lemma phi_p_sig (i k : ℕ) (hpar : (i + k) % 2 = 0) :
    ∫ u in (-1:ℝ)..1, RHSingDef0516.phi i u * RHLeg0503.p k u = sig i k := by
  have he : ((-1 : ℝ) ^ (i + k)) = 1 := Even.neg_one_pow (Nat.even_iff.mpr hpar)
  have hPr := RHSRed0516.Pr_OO i k
  have hT := RHPrEncl0511.Pr_T i k
  rw [he] at hPr hT
  have hc : halfWidth * RHRpExact0506.cc i * RHRpExact0506.cc k ≠ 0 := by
    have := RHPolyExp0522.cc_pos i; have := RHPolyExp0522.cc_pos k; have := halfWidth_pos; positivity
  have hsum : ∑ a : Fin 3, RHGammaExp0516.W a * ((1 + 1) * RHPairInt0516.OO i k (RHGammaExp0516.Sh a) 0) =
      2 * RHPrEncl0511.T i k := by
    have := hPr.symm.trans hT
    have h2 := mul_left_cancel₀ hc (this.trans (by ring : (1 + 1) * (halfWidth * RHRpExact0506.cc i * RHRpExact0506.cc k *
      RHPrEncl0511.T i k) = halfWidth * RHRpExact0506.cc i * RHRpExact0506.cc k * (2 * RHPrEncl0511.T i k)))
    exact h2
  rw [RHSRed0516.phi_p, he, hsum]; unfold sig; ring

lemma Gam_eq (o : Bool) (i k : I) :
    RHInterface0524.Gam o i k = sh (degree o i) * sh (degree o k) *
      ∫ u in (-1:ℝ)..1, RHSingDef0516.phi (degree o i) u * RHSingDef0516.phi (degree o k) u := by
  unfold RHInterface0524.Gam; rw [RHSxScale0516.gam_x, Lcc]

lemma sco_eq (o : Bool) (i : I) (m : ℕ) :
    RHInterface0524.sco o i m = sh (degree o i) * sh (degree o m) * sig (degree o i) (degree o m) := by
  unfold RHInterface0524.sco
  rw [RHSxScale0516.s_x, Lcc, phi_p_sig]
  unfold degree; cases o <;> simp <;> omega

/-! ### ρ -/

noncomputable def gam (i k : ℕ) : ℝ := ∫ u in (-1:ℝ)..1, RHSingDef0516.phi i u * RHSingDef0516.phi k u

noncomputable def rho (o : Bool) (ii kk : ℕ) : ℝ :=
  gam (degree o ii) (degree o kk) -
    ∑ m ∈ range 64, (2 * (degree o m : ℝ) + 1) / 2 * (sig (degree o ii) (degree o m) * sig (degree o kk) (degree o m))

lemma deg_lt (o : Bool) {n : ℕ} (hn : n < 32) : degree o n < 64 := by unfold degree; split_ifs <;> omega
lemma deg_lt128 (o : Bool) {n : ℕ} (hn : n < 64) : degree o n < 128 := by unfold degree; split_ifs <;> omega
lemma deg_par (o : Bool) (a b : ℕ) : (degree o a + degree o b) % 2 = 0 := by unfold degree; split_ifs <;> omega

lemma NKlen {T : List (List Ball)} (h : (List.range 64).all (fun j => decide (127 - j ≤ (T.getD j []).length)) = true) :
    ∀ j < 64, 127 - j ≤ (T.getD j []).length := by
  intro j hj; simpa [hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

lemma gam_mem (o : Bool) (ii kk : ℕ) (hi : ii < 32) (hk : kk < 32) :
    mem S (gam (degree o ii) (degree o kk)) (gamB (degree o ii) (degree o kk)) := by
  unfold gam
  rw [RHGamSound0523.gam_value _ _ (deg_par o ii kk)]
  exact RHGamSound0523.gamB_mem _ _ (deg_lt o hi) (deg_lt o hk) (NKlen (by decide +kernel)) (NKlen (by decide +kernel))

lemma rhoSum_mem (o : Bool) (di dk : ℕ) (hi : di < 64) (hk : dk < 64) : ∀ n ≤ 64,
    mem S (∑ m ∈ range n, (2 * (degree o m : ℝ) + 1) / 2 * (sig di (degree o m) * sig dk (degree o m)))
      (rhoSum o di dk n)
  | 0, _ => by simp only [rhoSum, sum_range_zero]; exact (mem_zero _ hS).mpr rfl
  | n + 1, hn => by
    rw [sum_range_succ]
    have h := mem_smul hS (2 * (degree o n : ℤ) + 1) (d := 2) (by norm_num)
      (mem_mulB hS (sig_mem di (degree o n) hi (deg_lt128 o (by omega))) (sig_mem dk (degree o n) hk (deg_lt128 o (by omega))))
    have := mem_add (rhoSum_mem o di dk hi hk n (by omega)) h
    simp only [rhoSum]; convert this using 1; push_cast; ring

lemma rhoB_mem (o : Bool) (ii kk : ℕ) (hi : ii < 32) (hk : kk < 32) :
    mem S (rho o ii kk) (rhoB o (gamTab o) ii kk) := by
  unfold rhoB rho
  have hg : gzz (gamTab o) ii kk = gamB (degree o ii) (degree o kk) := by
    unfold gzz gamTab gz
    simp [List.getD_eq_getElem?_getD, hi, hk]
  rw [hg]
  exact mem_sub (gam_mem o ii kk hi hk) (rhoSum_mem o _ _ (deg_lt o hi) (deg_lt o hk) 64 le_rfl)

/-! ### B, B′ and the column quadratic forms -/

noncomputable def Bn (o : Bool) (i j : ℕ) : ℝ :=
  if h : i < 32 ∧ j < 32 then RHConcreteParameters.concrete.B o ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

lemma Bn_eq (o : Bool) (i j : ℕ) (hi : i < 32) (hj : j < 32) : Bn o i j = ((Qn o i j : ℚ) : ℝ) := by
  unfold Bn Qn
  rw [dif_pos ⟨hi, hj⟩]
  show RHFixedCoordinates.B o _ _ = _
  cases o
  · simp only [RHFixedCoordinates.B, Bool.false_eq_true, if_false]
    exact RHBQ0512.even_eq ⟨i, hi⟩ ⟨j, hj⟩
  · simp only [RHFixedCoordinates.B, if_true]
    exact RHBQ0512.odd_eq ⟨i, hi⟩ ⟨j, hj⟩

lemma Bp_mem (o : Bool) (i j : ℕ) (hi : i < 32) (hj : j < 32) :
    mem S (Bn o i j * sh (degree o i)) (Bp o i j) := by
  rw [Bn_eq o i j hi hj]
  exact mem_mulB hS (mem_qBall hS _) (sq_mem _ (deg_lt o hi))

lemma colB_mem (o : Bool) (j : ℕ) (hj : j < 32) :
    VecMem S (fun i => if i < 32 then Bn o i j * sh (degree o i) else 0) (colB o j) := by
  intro i
  unfold colB gz
  by_cases hi : i < 32
  · simp [List.getD_eq_getElem?_getD, hi]; exact Bp_mem o i j hi hj
  · simp [List.getD_eq_getElem?_getD, hi]; exact (mem_zero _ hS).mpr rfl

lemma rhoRow_mem (o : Bool) (ii : ℕ) (hi : ii < 32) :
    VecMem S (fun kk => if kk < 32 then rho o ii kk else 0) ((rhoTab o (gamTab o)).getD ii []) := by
  intro kk
  unfold rhoTab gz
  by_cases hk : kk < 32
  · simp [List.getD_eq_getElem?_getD, hi, hk]; exact rhoB_mem o ii kk hi hk
  · simp [List.getD_eq_getElem?_getD, hi, hk]; exact (mem_zero _ hS).mpr rfl

lemma Tj_mem (o : Bool) (j : ℕ) (hj : j < 32) :
    mem S (∑ i ∈ range 32, Bn o i j * sh (degree o i) *
      ∑ k ∈ range 32, rho o i k * (Bn o k j * sh (degree o k))) (Tj o (rhoTab o (gamTab o)) j) := by
  have hc := colB_mem o j hj
  have hY : VecMem S (fun ii => if ii < 32 then ∑ k ∈ range 32, rho o ii k * (Bn o k j * sh (degree o k)) else 0)
      ((rhoTab o (gamTab o)).map (fun row => dotB S row (colB o j))) := by
    intro ii
    unfold gz
    by_cases hi : ii < 32
    · have hlen : ii < (rhoTab o (gamTab o)).length := by simp [rhoTab, hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some,
        Option.getD_some, if_pos hi]
      have := dot_mem hS (rhoRow_mem o ii hi) hc 32 (fun k hk => by simp [show ¬ k < 32 by omega])
        (fun k hk => by simp [show ¬ k < 32 by omega])
      have e : ∑ k ∈ range 32, (if k < 32 then rho o ii k else 0) * (if k < 32 then Bn o k j * sh (degree o k) else 0) =
          ∑ k ∈ range 32, rho o ii k * (Bn o k j * sh (degree o k)) :=
        sum_congr rfl (fun k hk => by simp [mem_range.mp hk])
      rw [e] at this
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] using this
    · simp [List.getD_eq_getElem?_getD, rhoTab, hi]; exact (mem_zero _ hS).mpr rfl
  have := dot_mem hS hc hY 32 (fun k hk => by simp [show ¬ k < 32 by omega]) (fun k hk => by simp [show ¬ k < 32 by omega])
  unfold Tj
  convert this using 1
  exact sum_congr rfl (fun i hi => by simp only [if_pos (mem_range.mp hi)])

/-! ### algebra -/

lemma Bn_fin (o : Bool) (i j : I) : Bn o i j = RHConcreteParameters.concrete.B o i j := by
  unfold Bn; rw [dif_pos ⟨i.isLt, j.isLt⟩]

lemma quad_eq (o : Bool) (j : I) :
    (∑ i : I, ∑ k : I, RHConcreteParameters.concrete.B o i j * RHConcreteParameters.concrete.B o k j *
        RHInterface0524.Gam o i k -
      ∑ m ∈ range 64, (∑ i : I, RHConcreteParameters.concrete.B o i j * RHInterface0524.sco o i m) ^ 2) =
    ∑ i ∈ range 32, Bn o i j * sh (degree o i) * ∑ k ∈ range 32, rho o i k * (Bn o k j * sh (degree o k)) := by
  unfold rho gam
  simp only [Finset.sum_range, ← Bn_fin, Gam_eq, sco_eq]
  have hsq : ∀ m : Fin 64, (∑ i : I, Bn o i j * (sh (degree o i) * sh (degree o m) * sig (degree o i) (degree o m))) ^ 2 =
      ∑ i : I, ∑ k : I, (Bn o i j * sh (degree o i)) * (Bn o k j * sh (degree o k)) *
        ((2 * (degree o m : ℝ) + 1) / 2 * (sig (degree o i) (degree o m) * sig (degree o k) (degree o m))) := by
    intro m
    rw [sq, sum_mul_sum]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => ?_))
    rw [← sh_sq (degree o m)]; ring
  rw [sum_congr rfl (fun m _ => hsq m), Finset.sum_comm (s := (Finset.univ : Finset (Fin 64))), ← sum_sub_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 64))), ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  rw [sub_mul, mul_sub, sum_mul, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl (fun m _ => by ring)

/-! ### the final inequality -/

lemma list_sum_range (f : ℕ → ℤ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, sum_range_succ]; simp

lemma list_sum_range_nat (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range_nat f n, sum_range_succ]; simp

lemma upper {x : ℝ} {b : Ball} (h : mem S x b) : x ≤ ((b.1 : ℝ) + b.2) / S := by
  unfold mem at h; rw [abs_le] at h; rw [add_div]; linarith [h.2]

lemma absB (o : Bool) (i j : ℕ) (hi : i < 32) (hj : j < 32) :
    |Bn o i j| ≤ (((qBall S (Qn o i j)).1.natAbs : ℝ) + 1) / (2 ^ 256 : ℝ) := by
  have h := mem_qBall hS (Qn o i j)
  rw [← Bn_eq o i j hi hj] at h
  unfold mem at h
  have hS' : (0:ℝ) < ((S : ℕ) : ℝ) := by positivity
  have h1 : (((qBall S (Qn o i j)).2 : ℕ) : ℝ) = 1 := by simp [qBall]
  rw [h1] at h
  have h3 := abs_sub_abs_le_abs_sub (Bn o i j) (((qBall S (Qn o i j)).1 : ℝ) / ((S : ℕ) : ℝ))
  rw [abs_div, abs_of_pos hS'] at h3
  have e : |((qBall S (Qn o i j)).1 : ℝ)| = ((qBall S (Qn o i j)).1.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e] at h3
  have hSv : ((S : ℕ) : ℝ) = 2 ^ 256 := by norm_num
  rw [hSv] at h h3
  rw [add_div]; linarith

lemma check_real (o : Bool) (h : check o (rhoTab o (gamTab o)) = true) :
    (1 + 1 / 10 ^ 4 : ℝ) * ((tot o (rhoTab o (gamTab o)) : ℝ) / S) +
      (1 + 10 ^ 4 : ℝ) * 2 * (81 / 100) * (1 / 10 ^ 28) * ((Esum o : ℝ) / (S : ℝ) ^ 2) ≤ 99 / 100 * (dMq o : ℝ) := by
  unfold check at h
  have hq := of_decide_eq_true h
  have : (((1 + 1 / 10 ^ 4 : ℚ) * ((tot o (rhoTab o (gamTab o)) : ℚ) / 2 ^ 256) +
    (1 + 10 ^ 4 : ℚ) * 2 * (81 / 100) * (1 / 10 ^ 28) * ((Esum o : ℚ) / (2 ^ 256) ^ 2) : ℚ) : ℝ) ≤
      ((99 / 100 * dMq o : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at this ⊢
  exact this

lemma dM_eq (o : Bool) : dM o = (dMq o : ℝ) := by
  unfold dM dMq
  cases o <;> simp [RHCertificateData.d128_odd_lower, RHCertificateData.d128_even_lower] <;> norm_num

lemma check_all (o : Bool) : check o (rhoTab o (gamTab o)) = true := by
  cases o
  · rw [← gamE_eq, ← rhoE_eq]; exact final_even
  · rw [← gamO_eq, ← rhoO_eq]; exact final_odd

theorem numBound : RHInterface0524.NumBound (1 / 10 ^ 14) (1 / 10 ^ 4) (99 / 100) := by
  intro o
  have hS' : (0:ℝ) < S := by positivity
  have hdM : 0 < dM o := by rw [dM_eq]; unfold dMq; cases o <;> norm_num
  -- quadratic parts
  have hq : ∀ j : I, (∑ i : I, ∑ k : I, RHConcreteParameters.concrete.B o i j * RHConcreteParameters.concrete.B o k j *
        RHInterface0524.Gam o i k -
      ∑ m ∈ range 64, (∑ i : I, RHConcreteParameters.concrete.B o i j * RHInterface0524.sco o i m) ^ 2) ≤
      (((Tj o (rhoTab o (gamTab o)) j).1 : ℝ) + (Tj o (rhoTab o (gamTab o)) j).2) / S := by
    intro j; rw [quad_eq]; exact upper (Tj_mem o j j.isLt)
  have hsumT : ∑ j : I, (((Tj o (rhoTab o (gamTab o)) j).1 : ℝ) + (Tj o (rhoTab o (gamTab o)) j).2) / S =
      (tot o (rhoTab o (gamTab o)) : ℝ) / S := by
    unfold tot
    rw [list_sum_range, ← sum_div]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun j => ((Tj o (rhoTab o (gamTab o)) j).1 : ℝ) + (Tj o (rhoTab o (gamTab o)) j).2) 32]
  -- |B| parts
  have hB : ∀ j : I, (∑ i : I, |RHConcreteParameters.concrete.B o i j|) ≤ (csum o j : ℝ) / 2 ^ 256 := by
    intro j
    have e1 : ∑ i : I, |RHConcreteParameters.concrete.B o i j| = ∑ i ∈ range 32, |Bn o i j| := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => |Bn o i j|) 32]; simp [Bn_fin]
    rw [e1]; unfold csum; rw [list_sum_range_nat]; push_cast; rw [sum_div]
    exact sum_le_sum (fun i hi => absB o i j (mem_range.mp hi) j.isLt)
  have hE : ∑ j : I, (1 / 10 ^ 14 * ∑ i : I, |RHConcreteParameters.concrete.B o i j|) ^ 2 ≤
      (1 / 10 ^ 28) * ((Esum o : ℝ) / (2 ^ 256 : ℝ) ^ 2) := by
    unfold Esum; rw [list_sum_range_nat]; push_cast
    calc ∑ j : I, (1 / 10 ^ 14 * ∑ i : I, |RHConcreteParameters.concrete.B o i j|) ^ 2
        ≤ ∑ j : I, (1 / 10 ^ 14 * ((csum o j : ℝ) / 2 ^ 256)) ^ 2 :=
          sum_le_sum (fun j _ => pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left (hB j) (by norm_num)) 2)
      _ = ∑ x ∈ range 32, (1 / 10 ^ 14 * ((csum o x : ℝ) / 2 ^ 256)) ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun x => (1 / 10 ^ 14 * ((csum o x : ℝ) / 2 ^ 256)) ^ 2) 32
      _ = _ := by rw [sum_div, mul_sum]; exact sum_congr rfl (fun x _ => by ring)
  have hL : 2 * halfWidth ≤ 2 * (81 / 100) := by linarith [RHEntryRepr0512.L_le]
  have hc := check_real o (check_all o)
  rw [← dM_eq] at hc
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdM]
  calc ∑ j : I, ((1 + 1 / 10 ^ 4) * (∑ i : I, ∑ k : I, RHConcreteParameters.concrete.B o i j *
          RHConcreteParameters.concrete.B o k j * RHInterface0524.Gam o i k -
          ∑ m ∈ range 64, (∑ i : I, RHConcreteParameters.concrete.B o i j * RHInterface0524.sco o i m) ^ 2) +
        (1 + 1 / (1 / 10 ^ 4)) * (2 * halfWidth) * (1 / 10 ^ 14 * ∑ i : I, |RHConcreteParameters.concrete.B o i j|) ^ 2)
      ≤ (1 + 1 / 10 ^ 4) * ((tot o (rhoTab o (gamTab o)) : ℝ) / S) +
        (1 + 10 ^ 4) * (2 * (81 / 100)) * ((1 / 10 ^ 28) * ((Esum o : ℝ) / (S : ℝ) ^ 2)) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← hsumT]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => hq j)) (by norm_num)
        · rw [show (1 + 1 / (1 / 10 ^ 4 : ℝ)) = 1 + 10 ^ 4 by norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hE (sum_nonneg (fun _ _ => sq_nonneg _))
            (by norm_num)
    _ ≤ 99 / 100 * dM o := by linarith

end RHRhoSound0524

