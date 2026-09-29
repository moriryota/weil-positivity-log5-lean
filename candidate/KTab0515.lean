import KTabData0515

/-! # 0515: soundness of the `K` table. -/

namespace RHKTab0515
open RHBall0504 RHBallVec0504 RHRec2D0515 RHTabCore0515 RHBaseNK0515

theorem K_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) j) (tab.getD j []) :=
  rows_mem (by positivity) _ kw_ii tab tab_chk1 tab_chk (by rw [tab_base]; exact kaBase_row)

end RHKTab0515

