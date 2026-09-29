import TpEncl0509
import TpRun0509_g0
import TpRun0509_g1
import TpRun0509_g2
import TpRun0509_g3
import TpRun0509_g4
import TpRun0509_g5
import TpRun0509_g6
import TpRun0509_g7

/-! # 0512: Tp data wrapper — uniform enclosure of `TS n 82 gq k (n+k+1)` for all n < 64, k < 128. -/

open RHBall0504 RHBallVec0504 RHCoarse0509 RHTpBall0509 RHTpEncl0509 RHProd0508
namespace RHTpAll0512

def tpSpecT : ℕ → List ((ℤ × ℕ) × (ℤ × ℕ))
  | 0 => RHTpRun0509.spec_0
  | 1 => RHTpRun0509.spec_1
  | 2 => RHTpRun0509.spec_2
  | 3 => RHTpRun0509.spec_3
  | 4 => RHTpRun0509.spec_4
  | 5 => RHTpRun0509.spec_5
  | 6 => RHTpRun0509.spec_6
  | 7 => RHTpRun0509.spec_7
  | 8 => RHTpRun0509.spec_8
  | 9 => RHTpRun0509.spec_9
  | 10 => RHTpRun0509.spec_10
  | 11 => RHTpRun0509.spec_11
  | 12 => RHTpRun0509.spec_12
  | 13 => RHTpRun0509.spec_13
  | 14 => RHTpRun0509.spec_14
  | 15 => RHTpRun0509.spec_15
  | 16 => RHTpRun0509.spec_16
  | 17 => RHTpRun0509.spec_17
  | 18 => RHTpRun0509.spec_18
  | 19 => RHTpRun0509.spec_19
  | 20 => RHTpRun0509.spec_20
  | 21 => RHTpRun0509.spec_21
  | 22 => RHTpRun0509.spec_22
  | 23 => RHTpRun0509.spec_23
  | 24 => RHTpRun0509.spec_24
  | 25 => RHTpRun0509.spec_25
  | 26 => RHTpRun0509.spec_26
  | 27 => RHTpRun0509.spec_27
  | 28 => RHTpRun0509.spec_28
  | 29 => RHTpRun0509.spec_29
  | 30 => RHTpRun0509.spec_30
  | 31 => RHTpRun0509.spec_31
  | 32 => RHTpRun0509.spec_32
  | 33 => RHTpRun0509.spec_33
  | 34 => RHTpRun0509.spec_34
  | 35 => RHTpRun0509.spec_35
  | 36 => RHTpRun0509.spec_36
  | 37 => RHTpRun0509.spec_37
  | 38 => RHTpRun0509.spec_38
  | 39 => RHTpRun0509.spec_39
  | 40 => RHTpRun0509.spec_40
  | 41 => RHTpRun0509.spec_41
  | 42 => RHTpRun0509.spec_42
  | 43 => RHTpRun0509.spec_43
  | 44 => RHTpRun0509.spec_44
  | 45 => RHTpRun0509.spec_45
  | 46 => RHTpRun0509.spec_46
  | 47 => RHTpRun0509.spec_47
  | 48 => RHTpRun0509.spec_48
  | 49 => RHTpRun0509.spec_49
  | 50 => RHTpRun0509.spec_50
  | 51 => RHTpRun0509.spec_51
  | 52 => RHTpRun0509.spec_52
  | 53 => RHTpRun0509.spec_53
  | 54 => RHTpRun0509.spec_54
  | 55 => RHTpRun0509.spec_55
  | 56 => RHTpRun0509.spec_56
  | 57 => RHTpRun0509.spec_57
  | 58 => RHTpRun0509.spec_58
  | 59 => RHTpRun0509.spec_59
  | 60 => RHTpRun0509.spec_60
  | 61 => RHTpRun0509.spec_61
  | 62 => RHTpRun0509.spec_62
  | 63 => RHTpRun0509.spec_63
  | _ => []

lemma tloop_len (S : ℕ) (W : List Ball) : ∀ (c k : ℕ) (b0 b1 : List Ball), (tloop S W c k b0 b1).length = c
  | 0, _, _, _ => rfl
  | c + 1, k, b0, b1 => by simp [tloop, tloop_len S W c]

theorem tp_gen (n : ℕ) (hchk : allWithin 384 (tpRun (2 ^ 512) n 82 gq 128) (tpSpecT n) = true) (k : ℕ) (hk : k < 128) :
    mem (2 ^ 128) (TS n 82 gq k (n + k + 1)) ((tpSpecT n).getD k ((0,0),(0,0))).2 := by
  have hS : 0 < 2 ^ 512 := by positivity
  have hlen : k < (tpRun (2 ^ 512) n 82 gq 128).length := by unfold tpRun; rw [tloop_len]; exact hk
  have hm := (tpRun_mem hS n 82 gq gq_den 128 k hk).2
  have hw := (allWithin_get 384 _ _ hchk k hlen).2
  exact mem_coarse (p := 128) (sh := 384) hm hw

theorem tp_chk_all : ∀ n < 64, allWithin 384 (tpRun (2 ^ 512) n 82 gq 128) (tpSpecT n) = true := by
  intro n hn
  interval_cases n
  · exact RHTpRun0509.chk_0
  · exact RHTpRun0509.chk_1
  · exact RHTpRun0509.chk_2
  · exact RHTpRun0509.chk_3
  · exact RHTpRun0509.chk_4
  · exact RHTpRun0509.chk_5
  · exact RHTpRun0509.chk_6
  · exact RHTpRun0509.chk_7
  · exact RHTpRun0509.chk_8
  · exact RHTpRun0509.chk_9
  · exact RHTpRun0509.chk_10
  · exact RHTpRun0509.chk_11
  · exact RHTpRun0509.chk_12
  · exact RHTpRun0509.chk_13
  · exact RHTpRun0509.chk_14
  · exact RHTpRun0509.chk_15
  · exact RHTpRun0509.chk_16
  · exact RHTpRun0509.chk_17
  · exact RHTpRun0509.chk_18
  · exact RHTpRun0509.chk_19
  · exact RHTpRun0509.chk_20
  · exact RHTpRun0509.chk_21
  · exact RHTpRun0509.chk_22
  · exact RHTpRun0509.chk_23
  · exact RHTpRun0509.chk_24
  · exact RHTpRun0509.chk_25
  · exact RHTpRun0509.chk_26
  · exact RHTpRun0509.chk_27
  · exact RHTpRun0509.chk_28
  · exact RHTpRun0509.chk_29
  · exact RHTpRun0509.chk_30
  · exact RHTpRun0509.chk_31
  · exact RHTpRun0509.chk_32
  · exact RHTpRun0509.chk_33
  · exact RHTpRun0509.chk_34
  · exact RHTpRun0509.chk_35
  · exact RHTpRun0509.chk_36
  · exact RHTpRun0509.chk_37
  · exact RHTpRun0509.chk_38
  · exact RHTpRun0509.chk_39
  · exact RHTpRun0509.chk_40
  · exact RHTpRun0509.chk_41
  · exact RHTpRun0509.chk_42
  · exact RHTpRun0509.chk_43
  · exact RHTpRun0509.chk_44
  · exact RHTpRun0509.chk_45
  · exact RHTpRun0509.chk_46
  · exact RHTpRun0509.chk_47
  · exact RHTpRun0509.chk_48
  · exact RHTpRun0509.chk_49
  · exact RHTpRun0509.chk_50
  · exact RHTpRun0509.chk_51
  · exact RHTpRun0509.chk_52
  · exact RHTpRun0509.chk_53
  · exact RHTpRun0509.chk_54
  · exact RHTpRun0509.chk_55
  · exact RHTpRun0509.chk_56
  · exact RHTpRun0509.chk_57
  · exact RHTpRun0509.chk_58
  · exact RHTpRun0509.chk_59
  · exact RHTpRun0509.chk_60
  · exact RHTpRun0509.chk_61
  · exact RHTpRun0509.chk_62
  · exact RHTpRun0509.chk_63

theorem tp_all (n k : ℕ) (hn : n < 64) (hk : k < 128) :
    mem (2 ^ 128) (TS n 82 gq k (n + k + 1)) ((tpSpecT n).getD k ((0,0),(0,0))).2 :=
  tp_gen n (tp_chk_all n hn) k hk

end RHTpAll0512

