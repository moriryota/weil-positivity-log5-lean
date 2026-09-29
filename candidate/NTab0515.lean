import NTabData0515

/-! # 0515: soundness of the `N` table. -/

namespace RHNTab0515
open RHBall0504 RHBallVec0504 RHRec2D0515 RHTabCore0515 RHBaseNK0515

theorem N_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x) ^ 2) j) (tab.getD j []) :=
  rows_mem (by positivity) _ RHNu0514.log2_ii tab tab_chk1 tab_chk (by rw [tab_base]; exact nuBase_row)

end RHNTab0515

