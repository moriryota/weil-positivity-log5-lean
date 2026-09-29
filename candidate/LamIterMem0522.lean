import LamCore0522

open scoped BigOperators
namespace RHLamIterMem0522
open RHBall0504 RHBallVec0504 RHBallDot0509 RHCcBall0510 RHCcSs0510
open RHLamDef0521 RHLamCore0522

lemma lamIter_pw (S : ℕ) (kB : Ball) (R : ℕ) :
    (lamIter S kB R).2.1 = pw S kB R := by
  induction R with
  | zero => rfl
  | succ R ih => simpa only [lamIter, pw] using congrArg (fun b => mulB S b kB) ih

lemma lamIter_xi_mem {S : ℕ} (hS : 0 < S) (kB : Ball) (R : ℕ) :
    VecMem S (ξ R) (lamIter S kB R).1 := by
  induction R with
  | zero => exact vecMem_vunit hS 0
  | succ R ih => exact vecMem_vX hS ih

theorem lamIter_mem {S : ℕ} (hS : 0 < S) {κ : ℝ} {kB : Ball}
    (hk : mem S κ kB) (R : ℕ) :
    VecMem S (acc κ R) (lamIter S kB R).2.2 := by
  induction R with
  | zero => intro l; simp [acc, lamIter, gz, mem]
  | succ R ih =>
    have hu : VecMem S (ξ (R+1)) (vX (lamIter S kB R).1) :=
      vecMem_vX hS (lamIter_xi_mem hS kB R)
    have hp : mem S (κ^(R+1)) (mulB S (lamIter S kB R).2.1 kB) := by
      rw [lamIter_pw]
      exact pw_mem hS hk (R+1)
    have hc : mem S (co κ R)
        (smul (if R % 2 = 0 then 1 else -1) (R+1) (mulB S (lamIter S kB R).2.1 kB)) := by
      have hm := mem_smul hS (if R % 2 = 0 then 1 else -1) (d := R+1) (by omega) hp
      convert hm using 1
      unfold co
      split_ifs <;> push_cast <;> ring
    have ha := vecMem_vadd ih (vecMem_vscaleB hS hc hu)
    intro l
    simpa only [lamIter, acc, Finset.sum_range_succ] using ha l

lemma mapI_length (f : ℕ → Ball → Ball) (i : ℕ) (bs : List Ball) :
    (mapI f i bs).length = bs.length := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp only [mapI, List.length_cons, ih]

lemma zipP_length (f : Ball → Ball → Ball) (as bs : List Ball) :
    (zipP f as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [zipP]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipP]
    | cons b bs => simp only [zipP, List.length_cons, ih, Nat.succ_max_succ]

lemma vadd_length (as bs : List Ball) : (vadd as bs).length = max as.length bs.length :=
  zipP_length _ as bs

lemma vscaleB_length (S : ℕ) (a : Ball) (bs : List Ball) :
    (vscaleB S a bs).length = bs.length := by simp [vscaleB]

lemma vX_length (bs : List Ball) : (vX bs).length = bs.length + 1 := by
  simp only [vX, vadd_length, List.length_cons, mapI_length, List.length_drop]
  omega

lemma lamIter_xi_length (S : ℕ) (kB : Ball) (R : ℕ) :
    (lamIter S kB R).1.length = R+1 := by
  induction R with
  | zero => simp [lamIter, vunit]
  | succ R ih => simpa only [lamIter, vX_length, ih]

lemma lamIter_acc_length_succ (S : ℕ) (kB : Ball) (R : ℕ) :
    (lamIter S kB (R+1)).2.2.length = R+2 := by
  induction R with
  | zero =>
    change (vadd [] (vscaleB S _ (vX (vunit S 0)))).length = 2
    simp [vadd_length, vscaleB_length, vX_length, vunit]
  | succ R ih =>
    change (vadd (lamIter S kB (R+1)).2.2 (vscaleB S _ (vX (lamIter S kB (R+1)).1))).length = R+1+2
    rw [vadd_length, vscaleB_length, vX_length, lamIter_xi_length, ih]
    omega

theorem lamIter_acc_length (S : ℕ) (kB : Ball) (R : ℕ) (hR : 0 < R) :
    (lamIter S kB R).2.2.length = R+1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  exact lamIter_acc_length_succ S kB r

theorem lamBase_length (S : ℕ) (kB : Ball) (R NL : ℕ) (hR : 0 < R) :
    (lamBase S kB R NL).length = min NL (R+1) := by
  rw [lamBase, mapI_length, List.length_take, lamIter_acc_length S kB R hR]

theorem lamBase_length_of_le (S : ℕ) (kB : Ball) (R NL : ℕ) (hR : 0 < R)
    (hNL : NL ≤ R+1) : (lamBase S kB R NL).length = NL := by
  rw [lamBase_length S kB R NL hR, min_eq_left hNL]

theorem lamBase_zero (S : ℕ) (kB : Ball) (NL : ℕ) : lamBase S kB 0 NL = [] := by
  simp [lamBase, lamIter, mapI]
end RHLamIterMem0522
