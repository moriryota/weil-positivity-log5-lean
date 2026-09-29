import LamAnalytic0522
import LamIterMem0522
import LamRadius0522

namespace RHLamBaseMem0522
open RHBall0504 RHBallVec0504 RHRec2D0515
open RHLamDef0521 RHLamCore0522 RHLamIterMem0522 RHLamRadius0522

lemma gz_take (bs : List Ball) (NL l : ℕ) (hl : l < (bs.take NL).length) :
    gz (bs.take NL) l = gz bs l := by
  have hb : l < bs.length := by rw [List.length_take] at hl; omega
  unfold gz
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hb, List.getElem_take]

/-- Exact requested contract; length coverage for R>0 is supplied separately. -/
theorem lamBase_mem {S : ℕ} (hS : 0 < S) {κ : ℝ} {kB : Ball}
    (hk : mem S κ kB) (h0 : 0 ≤ κ) (hK : kB.1+kB.2 < (S:ℤ))
    (R NL : ℕ) (hNL : NL ≤ R+1) :
    RowMem S (Mw (fun t => Real.log (1+κ*t)) 0) (lamBase S kB R NL) := by
  intro l hl
  have ht : l < ((lamIter S kB R).2.2.take NL).length := by
    simpa only [lamBase, mapI_length] using hl
  rw [lamBase, gz_mapI, if_pos ht, zero_add, gz_take _ _ _ ht]
  have hm := mem_smul hS 2 (d := 2*l+1) (by omega) (lamIter_mem hS hk R l)
  have hm' : mem S (approx κ R l) (smul 2 (2*l+1) (gz (lamIter S kB R).2.2 l)) := by
    convert hm using 1
    unfold approx
    push_cast
    ring
  apply mem_inflate hS hm'
  exact (RHLamAnalytic0522.approx_error h0 (kappa_lt_one hS hk h0 hK) R l).trans
    (radius_bound hS hk h0 hK R)

/-- The concrete requested 127-entry base row is not vacuous. -/
theorem lamBase_length_170_127 (S : ℕ) (kB : Ball) :
    (lamBase S kB 170 127).length = 127 :=
  lamBase_length_of_le S kB 170 127 (by norm_num) (by norm_num)

end RHLamBaseMem0522
