import LamBaseMem0522
import MkTabData2_0521
import MkTabData3_0521
import MkTabData4_0521
import FamDefs0522

/-! # 0523: soundness of the three `Mκ` tables (0521), using `lamBase_mem` (0522).
Row `j` encloses `Mw (log(1+κ_m t)) j`, `κ_m = (1−σ_m/2)/(1+σ_m/2)`. -/

namespace RHMkSound0523
open RHBall0504 RHRec2D0515 RHTabCore0515 RHConst0521

noncomputable def kap (m : ℕ) : ℝ := (1 - RHSingDef0516.σ m / 2) / (1 + RHSingDef0516.σ m / 2)

lemma kap_bounds {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) : 0 ≤ kap m ∧ kap m < 1 := by
  have h0 : 0 < RHSingDef0516.σ m := by
    rcases hm with rfl | rfl | rfl <;>
    · unfold RHSingDef0516.σ
      exact div_pos (Real.log_pos (by norm_num)) RHLog5Bridge.halfWidth_pos
  have h2 : RHSingDef0516.σ m ≤ 2 := RHGammaFull0516.sig_le (by rcases hm with rfl | rfl | rfl <;> norm_num)
    (by rcases hm with rfl | rfl | rfl <;> norm_num)
  unfold kap
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_lt_one (by linarith)]; linarith

theorem Mk2_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun t => Real.log (1 + kap 2 * t)) j) (RHMkTab2_0521.tab.getD j []) :=
  rows_mem (by positivity) _ (RHFRed0516.logk_ii (kap_bounds (Or.inl rfl)).1 (kap_bounds (Or.inl rfl)).2)
    RHMkTab2_0521.tab RHMkTab2_0521.tab_chk1 RHMkTab2_0521.tab_chk
    (by rw [RHMkTab2_0521.tab_base]
        exact RHLamBaseMem0522.lamBase_mem (by positivity) kap2_mem (kap_bounds (Or.inl rfl)).1
          (by decide +kernel) 170 127 (by norm_num))

theorem Mk3_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun t => Real.log (1 + kap 3 * t)) j) (RHMkTab3_0521.tab.getD j []) :=
  rows_mem (by positivity) _ (RHFRed0516.logk_ii (kap_bounds (Or.inr (Or.inl rfl))).1 (kap_bounds (Or.inr (Or.inl rfl))).2)
    RHMkTab3_0521.tab RHMkTab3_0521.tab_chk1 RHMkTab3_0521.tab_chk
    (by rw [RHMkTab3_0521.tab_base]
        exact RHLamBaseMem0522.lamBase_mem (by positivity) kap3_mem (kap_bounds (Or.inr (Or.inl rfl))).1
          (by decide +kernel) 170 127 (by norm_num))

theorem Mk4_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun t => Real.log (1 + kap 4 * t)) j) (RHMkTab4_0521.tab.getD j []) :=
  rows_mem (by positivity) _ (RHFRed0516.logk_ii (kap_bounds (Or.inr (Or.inr rfl))).1 (kap_bounds (Or.inr (Or.inr rfl))).2)
    RHMkTab4_0521.tab RHMkTab4_0521.tab_chk1 RHMkTab4_0521.tab_chk
    (by rw [RHMkTab4_0521.tab_base]
        exact RHLamBaseMem0522.lamBase_mem (by positivity) kap4_mem (kap_bounds (Or.inr (Or.inr rfl))).1
          (by decide +kernel) 170 127 (by norm_num))

end RHMkSound0523

