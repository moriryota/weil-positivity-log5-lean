import RpSpec0512_g0
import RpSpec0512_g1
import RpSpec0512_g2
import RpSpec0512_g3
import RpSpec0512_g4
import RpSpec0512_g5
import RpSpec0512_g6
import RpSpec0512_g7

/-! # 0512: Rp data wrapper — uniform coarse enclosure of `γ n 81 (rval rq) k` for all n < 64, k < 128. -/

open RHBall0504 RHBallVec0504 RHCoarse0509 RHAlgoBall0505 RHCcEncl0510 RHGForm0505
namespace RHRpAll0512

def rpSpecT : ℕ → List ((ℤ × ℕ) × (ℤ × ℕ))
  | 0 => RHRpSpec0512.rpSpec_0
  | 1 => RHRpSpec0512.rpSpec_1
  | 2 => RHRpSpec0512.rpSpec_2
  | 3 => RHRpSpec0512.rpSpec_3
  | 4 => RHRpSpec0512.rpSpec_4
  | 5 => RHRpSpec0512.rpSpec_5
  | 6 => RHRpSpec0512.rpSpec_6
  | 7 => RHRpSpec0512.rpSpec_7
  | 8 => RHRpSpec0512.rpSpec_8
  | 9 => RHRpSpec0512.rpSpec_9
  | 10 => RHRpSpec0512.rpSpec_10
  | 11 => RHRpSpec0512.rpSpec_11
  | 12 => RHRpSpec0512.rpSpec_12
  | 13 => RHRpSpec0512.rpSpec_13
  | 14 => RHRpSpec0512.rpSpec_14
  | 15 => RHRpSpec0512.rpSpec_15
  | 16 => RHRpSpec0512.rpSpec_16
  | 17 => RHRpSpec0512.rpSpec_17
  | 18 => RHRpSpec0512.rpSpec_18
  | 19 => RHRpSpec0512.rpSpec_19
  | 20 => RHRpSpec0512.rpSpec_20
  | 21 => RHRpSpec0512.rpSpec_21
  | 22 => RHRpSpec0512.rpSpec_22
  | 23 => RHRpSpec0512.rpSpec_23
  | 24 => RHRpSpec0512.rpSpec_24
  | 25 => RHRpSpec0512.rpSpec_25
  | 26 => RHRpSpec0512.rpSpec_26
  | 27 => RHRpSpec0512.rpSpec_27
  | 28 => RHRpSpec0512.rpSpec_28
  | 29 => RHRpSpec0512.rpSpec_29
  | 30 => RHRpSpec0512.rpSpec_30
  | 31 => RHRpSpec0512.rpSpec_31
  | 32 => RHRpSpec0512.rpSpec_32
  | 33 => RHRpSpec0512.rpSpec_33
  | 34 => RHRpSpec0512.rpSpec_34
  | 35 => RHRpSpec0512.rpSpec_35
  | 36 => RHRpSpec0512.rpSpec_36
  | 37 => RHRpSpec0512.rpSpec_37
  | 38 => RHRpSpec0512.rpSpec_38
  | 39 => RHRpSpec0512.rpSpec_39
  | 40 => RHRpSpec0512.rpSpec_40
  | 41 => RHRpSpec0512.rpSpec_41
  | 42 => RHRpSpec0512.rpSpec_42
  | 43 => RHRpSpec0512.rpSpec_43
  | 44 => RHRpSpec0512.rpSpec_44
  | 45 => RHRpSpec0512.rpSpec_45
  | 46 => RHRpSpec0512.rpSpec_46
  | 47 => RHRpSpec0512.rpSpec_47
  | 48 => RHRpSpec0512.rpSpec_48
  | 49 => RHRpSpec0512.rpSpec_49
  | 50 => RHRpSpec0512.rpSpec_50
  | 51 => RHRpSpec0512.rpSpec_51
  | 52 => RHRpSpec0512.rpSpec_52
  | 53 => RHRpSpec0512.rpSpec_53
  | 54 => RHRpSpec0512.rpSpec_54
  | 55 => RHRpSpec0512.rpSpec_55
  | 56 => RHRpSpec0512.rpSpec_56
  | 57 => RHRpSpec0512.rpSpec_57
  | 58 => RHRpSpec0512.rpSpec_58
  | 59 => RHRpSpec0512.rpSpec_59
  | 60 => RHRpSpec0512.rpSpec_60
  | 61 => RHRpSpec0512.rpSpec_61
  | 62 => RHRpSpec0512.rpSpec_62
  | 63 => RHRpSpec0512.rpSpec_63
  | _ => []

lemma pairUp_len : ∀ (as bs : List Ball), (pairUp as bs).length = max as.length bs.length
  | a :: as, b :: bs => by simp [pairUp, pairUp_len as bs, Nat.succ_max_succ]
  | a :: as, [] => by simp [pairUp, pairUp_len as []]
  | [], b :: bs => by simp [pairUp, pairUp_len [] bs]
  | [], [] => by simp [pairUp]
termination_by as bs => as.length + bs.length

theorem rp_gen (n : ℕ) (hchk : allWithin 384 (pairUp (run (2 ^ 512) n RHEntry22_0505.rq 81).2.2
    (List.replicate 128 (0, 0))) (rpSpecT n) = true) (k : ℕ) (hk : k < 128) :
    mem (2 ^ 128) (γ n 81 (rval RHEntry22_0505.rq) k) ((rpSpecT n).getD k ((0,0),(0,0))).1 := by
  have hS : 0 < 2 ^ 512 := by positivity
  have hm := (run_mem hS n RHEntry22_0505.rq RHRpCoef0506.rden_pos 81).2.2 k
  generalize hacc : (run (2 ^ 512) n RHEntry22_0505.rq 81).2.2 = acc at hchk hm
  have hlen : k < (pairUp acc (List.replicate 128 (0, 0))).length := by
    rw [pairUp_len, List.length_replicate]; exact lt_of_lt_of_le hk (le_max_right _ _)
  have hw := (allWithin_get 384 (pairUp acc (List.replicate 128 (0, 0))) (rpSpecT n) hchk k hlen).1
  rw [pairUp_get] at hw
  exact mem_coarse (p := 128) (sh := 384) hm hw

theorem rp_chk_all : ∀ n < 64, allWithin 384 (pairUp (run (2 ^ 512) n RHEntry22_0505.rq 81).2.2
    (List.replicate 128 (0, 0))) (rpSpecT n) = true := by
  intro n hn
  interval_cases n
  · exact RHRpSpec0512.rpc_0
  · exact RHRpSpec0512.rpc_1
  · exact RHRpSpec0512.rpc_2
  · exact RHRpSpec0512.rpc_3
  · exact RHRpSpec0512.rpc_4
  · exact RHRpSpec0512.rpc_5
  · exact RHRpSpec0512.rpc_6
  · exact RHRpSpec0512.rpc_7
  · exact RHRpSpec0512.rpc_8
  · exact RHRpSpec0512.rpc_9
  · exact RHRpSpec0512.rpc_10
  · exact RHRpSpec0512.rpc_11
  · exact RHRpSpec0512.rpc_12
  · exact RHRpSpec0512.rpc_13
  · exact RHRpSpec0512.rpc_14
  · exact RHRpSpec0512.rpc_15
  · exact RHRpSpec0512.rpc_16
  · exact RHRpSpec0512.rpc_17
  · exact RHRpSpec0512.rpc_18
  · exact RHRpSpec0512.rpc_19
  · exact RHRpSpec0512.rpc_20
  · exact RHRpSpec0512.rpc_21
  · exact RHRpSpec0512.rpc_22
  · exact RHRpSpec0512.rpc_23
  · exact RHRpSpec0512.rpc_24
  · exact RHRpSpec0512.rpc_25
  · exact RHRpSpec0512.rpc_26
  · exact RHRpSpec0512.rpc_27
  · exact RHRpSpec0512.rpc_28
  · exact RHRpSpec0512.rpc_29
  · exact RHRpSpec0512.rpc_30
  · exact RHRpSpec0512.rpc_31
  · exact RHRpSpec0512.rpc_32
  · exact RHRpSpec0512.rpc_33
  · exact RHRpSpec0512.rpc_34
  · exact RHRpSpec0512.rpc_35
  · exact RHRpSpec0512.rpc_36
  · exact RHRpSpec0512.rpc_37
  · exact RHRpSpec0512.rpc_38
  · exact RHRpSpec0512.rpc_39
  · exact RHRpSpec0512.rpc_40
  · exact RHRpSpec0512.rpc_41
  · exact RHRpSpec0512.rpc_42
  · exact RHRpSpec0512.rpc_43
  · exact RHRpSpec0512.rpc_44
  · exact RHRpSpec0512.rpc_45
  · exact RHRpSpec0512.rpc_46
  · exact RHRpSpec0512.rpc_47
  · exact RHRpSpec0512.rpc_48
  · exact RHRpSpec0512.rpc_49
  · exact RHRpSpec0512.rpc_50
  · exact RHRpSpec0512.rpc_51
  · exact RHRpSpec0512.rpc_52
  · exact RHRpSpec0512.rpc_53
  · exact RHRpSpec0512.rpc_54
  · exact RHRpSpec0512.rpc_55
  · exact RHRpSpec0512.rpc_56
  · exact RHRpSpec0512.rpc_57
  · exact RHRpSpec0512.rpc_58
  · exact RHRpSpec0512.rpc_59
  · exact RHRpSpec0512.rpc_60
  · exact RHRpSpec0512.rpc_61
  · exact RHRpSpec0512.rpc_62
  · exact RHRpSpec0512.rpc_63

theorem rp_all (n k : ℕ) (hn : n < 64) (hk : k < 128) :
    mem (2 ^ 128) (γ n 81 (rval RHEntry22_0505.rq) k) ((rpSpecT n).getD k ((0,0),(0,0))).1 :=
  rp_gen n (rp_chk_all n hn) k hk

end RHRpAll0512

