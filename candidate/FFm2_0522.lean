import FFc2_0_0522
import FFc2_1_0522
import FFc2_2_0522
import FFc2_3_0522
import FFc2_4_0522
import FFc2_5_0522
import FFc2_6_0522
import FFc2_7_0522

/-! # 0522: F stage m = 2 assembled from 8 chunks: `Fm.getD i [] = fRow (famA.getD i [])` (i < 64). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RHFFm2_0522
open RHBall0504 RHFRow2_0522

def chunk : ℕ → List (List Ball)
  | 0 => RHFFc2_0_0522.FmC
  | 1 => RHFFc2_1_0522.FmC
  | 2 => RHFFc2_2_0522.FmC
  | 3 => RHFFc2_3_0522.FmC
  | 4 => RHFFc2_4_0522.FmC
  | 5 => RHFFc2_5_0522.FmC
  | 6 => RHFFc2_6_0522.FmC
  | _ => RHFFc2_7_0522.FmC

def Fm : List (List Ball) := RHFFc2_0_0522.FmC ++ RHFFc2_1_0522.FmC ++ RHFFc2_2_0522.FmC ++ RHFFc2_3_0522.FmC ++ RHFFc2_4_0522.FmC ++ RHFFc2_5_0522.FmC ++ RHFFc2_6_0522.FmC ++ RHFFc2_7_0522.FmC

theorem Fm_chunk : (List.range 64).all (fun i => Fm.getD i [] == (chunk (i / 8)).getD (i % 8) []) = true := by
  decide +kernel

theorem key (a i : ℕ) (hr : i % 8 < 8) :
    ((List.range 8).map (fun r => fRow (RHFamA_0522.famA2.getD (a + r) []))).getD (i % 8) [] =
      fRow (RHFamA_0522.famA2.getD (a + i % 8) []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]; rfl

theorem chunk_row (i : ℕ) (hi : i < 64) : (chunk (i / 8)).getD (i % 8) [] = fRow (RHFamA_0522.famA2.getD i []) := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hc : i / 8 < 8 := by omega
  interval_cases h : i / 8 <;> simp only [chunk]
  · rw [RHFFc2_0_0522.c_eq, key _ _ hr, show 0 + i % 8 = i by omega]
  · rw [RHFFc2_1_0522.c_eq, key _ _ hr, show 8 + i % 8 = i by omega]
  · rw [RHFFc2_2_0522.c_eq, key _ _ hr, show 16 + i % 8 = i by omega]
  · rw [RHFFc2_3_0522.c_eq, key _ _ hr, show 24 + i % 8 = i by omega]
  · rw [RHFFc2_4_0522.c_eq, key _ _ hr, show 32 + i % 8 = i by omega]
  · rw [RHFFc2_5_0522.c_eq, key _ _ hr, show 40 + i % 8 = i by omega]
  · rw [RHFFc2_6_0522.c_eq, key _ _ hr, show 48 + i % 8 = i by omega]
  · rw [RHFFc2_7_0522.c_eq, key _ _ hr, show 56 + i % 8 = i by omega]

theorem Fm_row (i : ℕ) (hi : i < 64) : Fm.getD i [] = fRow (RHFamA_0522.famA2.getD i []) := by
  have h := (List.all_eq_true.mp Fm_chunk) i (List.mem_range.mpr hi)
  simp only [beq_iff_eq] at h
  rw [h, chunk_row i hi]

end RHFFm2_0522
