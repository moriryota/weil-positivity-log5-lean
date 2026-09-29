import PrRow0511
import PrRun0511_g0
import PrRun0511_g1
import PrRun2_0511_g4
import PrRun2_0511_g5
import PrRun2_0511_g6
import PrRun2_0511_g7
import PrRun2_0511_g8
import PrRun2_0511_g9
import PrRun2_0511_g10
import PrRun2_0511_g11
import PrRun2_0511_g12
import PrRun2_0511_g13
import PrRun2_0511_g14
import PrRun2_0511_g15

/-! # 0512: Pr data wrapper — uniform coarse enclosure of `T n k` for all n < 64, k < 128. -/

open RHBall0504 RHCoarse0509 RHPrEncl0511 RHPrRow0511
namespace RHPrAll0512

def prSpecT : ℕ → List ((ℤ × ℕ) × (ℤ × ℕ))
  | 0 => RHPrRun0511.spec_0
  | 1 => RHPrRun0511.spec_1
  | 2 => RHPrRun0511.spec_2
  | 3 => RHPrRun0511.spec_3
  | 4 => RHPrRun0511.spec_4
  | 5 => RHPrRun0511.spec_5
  | 6 => RHPrRun0511.spec_6
  | 7 => RHPrRun0511.spec_7
  | 8 => RHPrRun0511.spec_8
  | 9 => RHPrRun0511.spec_9
  | 10 => RHPrRun0511.spec_10
  | 11 => RHPrRun0511.spec_11
  | 12 => RHPrRun0511.spec_12
  | 13 => RHPrRun0511.spec_13
  | 14 => RHPrRun0511.spec_14
  | 15 => RHPrRun0511.spec_15
  | 16 => RHPrRun2_0511.spec_16
  | 17 => RHPrRun2_0511.spec_17
  | 18 => RHPrRun2_0511.spec_18
  | 19 => RHPrRun2_0511.spec_19
  | 20 => RHPrRun2_0511.spec_20
  | 21 => RHPrRun2_0511.spec_21
  | 22 => RHPrRun2_0511.spec_22
  | 23 => RHPrRun2_0511.spec_23
  | 24 => RHPrRun2_0511.spec_24
  | 25 => RHPrRun2_0511.spec_25
  | 26 => RHPrRun2_0511.spec_26
  | 27 => RHPrRun2_0511.spec_27
  | 28 => RHPrRun2_0511.spec_28
  | 29 => RHPrRun2_0511.spec_29
  | 30 => RHPrRun2_0511.spec_30
  | 31 => RHPrRun2_0511.spec_31
  | 32 => RHPrRun2_0511.spec_32
  | 33 => RHPrRun2_0511.spec_33
  | 34 => RHPrRun2_0511.spec_34
  | 35 => RHPrRun2_0511.spec_35
  | 36 => RHPrRun2_0511.spec_36
  | 37 => RHPrRun2_0511.spec_37
  | 38 => RHPrRun2_0511.spec_38
  | 39 => RHPrRun2_0511.spec_39
  | 40 => RHPrRun2_0511.spec_40
  | 41 => RHPrRun2_0511.spec_41
  | 42 => RHPrRun2_0511.spec_42
  | 43 => RHPrRun2_0511.spec_43
  | 44 => RHPrRun2_0511.spec_44
  | 45 => RHPrRun2_0511.spec_45
  | 46 => RHPrRun2_0511.spec_46
  | 47 => RHPrRun2_0511.spec_47
  | 48 => RHPrRun2_0511.spec_48
  | 49 => RHPrRun2_0511.spec_49
  | 50 => RHPrRun2_0511.spec_50
  | 51 => RHPrRun2_0511.spec_51
  | 52 => RHPrRun2_0511.spec_52
  | 53 => RHPrRun2_0511.spec_53
  | 54 => RHPrRun2_0511.spec_54
  | 55 => RHPrRun2_0511.spec_55
  | 56 => RHPrRun2_0511.spec_56
  | 57 => RHPrRun2_0511.spec_57
  | 58 => RHPrRun2_0511.spec_58
  | 59 => RHPrRun2_0511.spec_59
  | 60 => RHPrRun2_0511.spec_60
  | 61 => RHPrRun2_0511.spec_61
  | 62 => RHPrRun2_0511.spec_62
  | 63 => RHPrRun2_0511.spec_63
  | _ => []

lemma rowFrom_len (a2 a3 a4 : List Ball) (w2 w3 w4 : Ball) : ∀ (B2 B3 B4 : List (List Ball)),
    B2.length = 128 → B3.length = 128 → B4.length = 128 → (rowFrom a2 a3 a4 w2 w3 w4 B2 B3 B4).length = 128 := by
  have key : ∀ (c : ℕ) (B2 B3 B4 : List (List Ball)), B2.length = c → B3.length = c → B4.length = c →
      (rowFrom a2 a3 a4 w2 w3 w4 B2 B3 B4).length = c := by
    intro c; induction c with
    | zero => intro B2 B3 B4 h2 _ _; rw [List.length_eq_zero_iff.mp h2]; simp [rowFrom]
    | succ c ih =>
        intro B2 B3 B4 h2 h3 h4
        match B2, B3, B4, h2, h3, h4 with
        | b2 :: B2, b3 :: B3, b4 :: B4, h2, h3, h4 =>
            simp only [rowFrom, List.length_cons]; simp at h2 h3 h4; rw [ih B2 B3 B4 h2 h3 h4]
  exact key 128

/-- Generic: from a structural-row check with `a_m = R_m.1[n]`. -/
theorem pr_gen_row (n : ℕ)
    (hchk : allWithin 384 (rowFrom (R2.1.getD n []) (R3.1.getD n []) (R4.1.getD n []) R2.2.2 R3.2.2 R4.2.2
      R2.2.1 R3.2.1 R4.2.1) (prSpecT n) = true) (hn : n < 64) (k : ℕ) (hk : k < 128) :
    mem (2 ^ 128) (T n k) ((prSpecT n).getD k ((0,0),(0,0))).1 := by
  have hS : 0 < S512 := hS
  have hlen : k < (rowFrom (R2.1.getD n []) (R3.1.getD n []) (R4.1.getD n []) R2.2.2 R3.2.2 R4.2.2
      R2.2.1 R3.2.1 R4.2.1).length := by
    rw [rowFrom_len _ _ _ _ _ _ _ _ _ (by rw [R2, lenB]) (by rw [R3, lenB]) (by rw [R4, lenB])]; exact hk
  have hw := (allWithin_get 384 _ _ hchk k hlen).1
  rw [row_eq_prT n k hk] at hw
  exact mem_coarse (p := 128) (sh := 384) (prT_mem n k hn hk) hw

/-- Generic: from a `List.range` row check. -/
theorem pr_gen_map (n : ℕ)
    (hchk : allWithin 384 ((List.range 128).map (fun k => (prT R2 R3 R4 n k, ((0 : ℤ), (0 : ℕ))))) (prSpecT n) = true)
    (hn : n < 64) (k : ℕ) (hk : k < 128) :
    mem (2 ^ 128) (T n k) ((prSpecT n).getD k ((0,0),(0,0))).1 := by
  have hlen : k < ((List.range 128).map (fun k => (prT R2 R3 R4 n k, ((0 : ℤ), (0 : ℕ))))).length := by simpa using hk
  have hw := (allWithin_get 384 _ _ hchk k hlen).1
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_range] at hw
  exact mem_coarse (p := 128) (sh := 384) (prT_mem n k hn hk) hw

theorem pr_all (n k : ℕ) (hn : n < 64) (hk : k < 128) :
    mem (2 ^ 128) (T n k) ((prSpecT n).getD k ((0,0),(0,0))).1 := by
  interval_cases n
  · exact pr_gen_map 0 RHPrRun0511.chk_0 (by norm_num) k hk
  · exact pr_gen_map 1 RHPrRun0511.chk_1 (by norm_num) k hk
  · exact pr_gen_map 2 RHPrRun0511.chk_2 (by norm_num) k hk
  · exact pr_gen_map 3 RHPrRun0511.chk_3 (by norm_num) k hk
  · exact pr_gen_map 4 RHPrRun0511.chk_4 (by norm_num) k hk
  · exact pr_gen_map 5 RHPrRun0511.chk_5 (by norm_num) k hk
  · exact pr_gen_map 6 RHPrRun0511.chk_6 (by norm_num) k hk
  · exact pr_gen_map 7 RHPrRun0511.chk_7 (by norm_num) k hk
  · exact pr_gen_map 8 RHPrRun0511.chk_8 (by norm_num) k hk
  · exact pr_gen_map 9 RHPrRun0511.chk_9 (by norm_num) k hk
  · exact pr_gen_map 10 RHPrRun0511.chk_10 (by norm_num) k hk
  · exact pr_gen_map 11 RHPrRun0511.chk_11 (by norm_num) k hk
  · exact pr_gen_map 12 RHPrRun0511.chk_12 (by norm_num) k hk
  · exact pr_gen_map 13 RHPrRun0511.chk_13 (by norm_num) k hk
  · exact pr_gen_map 14 RHPrRun0511.chk_14 (by norm_num) k hk
  · exact pr_gen_map 15 RHPrRun0511.chk_15 (by norm_num) k hk
  · exact pr_gen_row 16 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_16; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_16) (by norm_num) k hk
  · exact pr_gen_row 17 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_17; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_17) (by norm_num) k hk
  · exact pr_gen_row 18 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_18; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_18) (by norm_num) k hk
  · exact pr_gen_row 19 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_19; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_19) (by norm_num) k hk
  · exact pr_gen_row 20 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_20; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_20) (by norm_num) k hk
  · exact pr_gen_row 21 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_21; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_21) (by norm_num) k hk
  · exact pr_gen_row 22 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_22; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_22) (by norm_num) k hk
  · exact pr_gen_row 23 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_23; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_23) (by norm_num) k hk
  · exact pr_gen_row 24 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_24; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_24) (by norm_num) k hk
  · exact pr_gen_row 25 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_25; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_25) (by norm_num) k hk
  · exact pr_gen_row 26 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_26; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_26) (by norm_num) k hk
  · exact pr_gen_row 27 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_27; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_27) (by norm_num) k hk
  · exact pr_gen_row 28 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_28; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_28) (by norm_num) k hk
  · exact pr_gen_row 29 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_29; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_29) (by norm_num) k hk
  · exact pr_gen_row 30 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_30; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_30) (by norm_num) k hk
  · exact pr_gen_row 31 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_31; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_31) (by norm_num) k hk
  · exact pr_gen_row 32 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_32; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_32) (by norm_num) k hk
  · exact pr_gen_row 33 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_33; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_33) (by norm_num) k hk
  · exact pr_gen_row 34 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_34; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_34) (by norm_num) k hk
  · exact pr_gen_row 35 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_35; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_35) (by norm_num) k hk
  · exact pr_gen_row 36 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_36; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_36) (by norm_num) k hk
  · exact pr_gen_row 37 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_37; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_37) (by norm_num) k hk
  · exact pr_gen_row 38 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_38; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_38) (by norm_num) k hk
  · exact pr_gen_row 39 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_39; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_39) (by norm_num) k hk
  · exact pr_gen_row 40 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_40; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_40) (by norm_num) k hk
  · exact pr_gen_row 41 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_41; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_41) (by norm_num) k hk
  · exact pr_gen_row 42 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_42; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_42) (by norm_num) k hk
  · exact pr_gen_row 43 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_43; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_43) (by norm_num) k hk
  · exact pr_gen_row 44 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_44; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_44) (by norm_num) k hk
  · exact pr_gen_row 45 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_45; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_45) (by norm_num) k hk
  · exact pr_gen_row 46 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_46; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_46) (by norm_num) k hk
  · exact pr_gen_row 47 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_47; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_47) (by norm_num) k hk
  · exact pr_gen_row 48 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_48; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_48) (by norm_num) k hk
  · exact pr_gen_row 49 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_49; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_49) (by norm_num) k hk
  · exact pr_gen_row 50 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_50; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_50) (by norm_num) k hk
  · exact pr_gen_row 51 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_51; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_51) (by norm_num) k hk
  · exact pr_gen_row 52 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_52; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_52) (by norm_num) k hk
  · exact pr_gen_row 53 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_53; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_53) (by norm_num) k hk
  · exact pr_gen_row 54 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_54; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_54) (by norm_num) k hk
  · exact pr_gen_row 55 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_55; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_55) (by norm_num) k hk
  · exact pr_gen_row 56 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_56; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_56) (by norm_num) k hk
  · exact pr_gen_row 57 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_57; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_57) (by norm_num) k hk
  · exact pr_gen_row 58 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_58; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_58) (by norm_num) k hk
  · exact pr_gen_row 59 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_59; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_59) (by norm_num) k hk
  · exact pr_gen_row 60 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_60; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_60) (by norm_num) k hk
  · exact pr_gen_row 61 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_61; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_61) (by norm_num) k hk
  · exact pr_gen_row 62 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_62; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_62) (by norm_num) k hk
  · exact pr_gen_row 63 (by obtain ⟨h2, h3, h4⟩ := RHPrRun2_0511.hA_63; rw [h2, h3, h4]; exact RHPrRun2_0511.chk_63) (by norm_num) k hk

end RHPrAll0512

