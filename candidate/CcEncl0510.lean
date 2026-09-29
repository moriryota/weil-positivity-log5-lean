import CcBall0510

/-! # 0510: rigorous enclosures of `Cc n` and `Ss n` (all `n`)

`xB ⊇ L/2` (from `log 5 ∈ [l5L, l5H]`); `bnd 40 ≤ 10⁻⁶⁰`; kernel check of
`ceV (2^512) 40 xB false/true` against coarse (2^128) specs; for `n ≥ 40`, `ce 40 odd n = 0`.
`|Cc n − L c_n c/2^128| ≤ L c_n (r/2^128 + 10⁻⁶⁰)` (and `Ss`). -/

open Finset
open scoped BigOperators

namespace RHCcEncl0510
open RHConditionalLog5 RHBall0504 RHBallVec0504 RHCoarse0509 RHCcSs0510 RHCcBall0510 RHLog5Bridge RHRpExact0506 RHEntry00Bounds0495

def xB : Ball := (5394758601271047550189696958505422657118018912329563435348084249499546742363846674406950684925763164193043462224946741509804586150270840347845978045319594, 16759759912428246374467531247757307659349207275740491722154451804652205037591933721002342872708629284612539822733107563569)

lemma xB_mem : mem (2 ^ 512) (halfWidth / 2) xB := by
  have h5 := b_l5
  have c1 : ((5394758601271047550189696958505422657118018912329563435348084249499546742363846674406950684925763164193043462224946741509804586150270840347845978045319594 : ℤ) : ℚ) / 2 ^ 512 - ((16759759912428246374467531247757307659349207275740491722154451804652205037591933721002342872708629284612539822733107563569 : ℕ) : ℚ) / 2 ^ 512 ≤ l5L / 4 := by decide +kernel
  have c2 : l5H / 4 ≤ ((5394758601271047550189696958505422657118018912329563435348084249499546742363846674406950684925763164193043462224946741509804586150270840347845978045319594 : ℤ) : ℚ) / 2 ^ 512 + ((16759759912428246374467531247757307659349207275740491722154451804652205037591933721002342872708629284612539822733107563569 : ℕ) : ℚ) / 2 ^ 512 := by decide +kernel
  have c1' := (Rat.cast_le (K := ℝ)).mpr c1
  have c2' := (Rat.cast_le (K := ℝ)).mpr c2
  push_cast at c1' c2'
  unfold mem xB; simp only
  rw [abs_le]; unfold halfWidth; push_cast
  constructor <;> linarith [h5.1, h5.2]

lemma bnd_le : bnd 40 ≤ 1 / 10 ^ 60 := by
  have h5 := b_l5.2
  have hx0 : 0 ≤ halfWidth / 2 := by have := halfWidth_pos; positivity
  have hx : halfWidth / 2 ≤ ((l5H / 4 : ℚ) : ℝ) := by unfold halfWidth; push_cast; linarith
  have hp : (halfWidth / 2) ^ 40 ≤ ((l5H / 4 : ℚ) : ℝ) ^ 40 := pow_le_pow_left₀ hx0 hx 40
  have hq : 2 * ((l5H / 4) ^ 40 * ((41 : ℚ) / ((Nat.factorial 40 : ℚ) * 40))) ≤ 1 / 10 ^ 60 := by decide +kernel
  have hq' := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hq' hp
  unfold bnd
  have hk : (0:ℝ) ≤ ((Nat.succ 40 : ℕ) : ℝ) / ((Nat.factorial 40 : ℕ) * (40 : ℕ)) := by positivity
  have e : ((Nat.succ 40 : ℕ) : ℝ) / ((Nat.factorial 40 : ℕ) * (40 : ℕ)) = (41 : ℝ) / ((Nat.factorial 40 : ℝ) * 40) := by
    push_cast; ring
  rw [e] at hk ⊢
  nlinarith [mul_le_mul_of_nonneg_right hp hk]

def pairUp : List Ball → List Ball → List (Ball × Ball)
  | a :: as, b :: bs => (a, b) :: pairUp as bs
  | a :: as, [] => (a, (0, 0)) :: pairUp as []
  | [], b :: bs => ((0, 0), b) :: pairUp [] bs
  | [], [] => []
termination_by as bs => as.length + bs.length

lemma pairUp_get : ∀ (as bs : List Ball) (k : ℕ), (pairUp as bs).getD k ((0,0),(0,0)) = (gz as k, gz bs k)
  | a :: as, b :: bs, 0 => by simp [pairUp]
  | a :: as, b :: bs, k + 1 => by simp only [pairUp, List.getD_cons_succ, gz_cons_succ]; exact pairUp_get as bs k
  | a :: as, [], 0 => by simp [pairUp]
  | a :: as, [], k + 1 => by simp only [pairUp, List.getD_cons_succ, gz_cons_succ, gz_nil]; simpa using pairUp_get as [] k
  | [], b :: bs, 0 => by simp [pairUp]
  | [], b :: bs, k + 1 => by simp only [pairUp, List.getD_cons_succ, gz_cons_succ, gz_nil]; simpa using pairUp_get [] bs k
  | [], [], k => by simp [pairUp]
termination_by as bs => as.length + bs.length

def ccSpec : List ((ℤ × ℕ) × (ℤ × ℕ)) := [((699077079371355008464502618064489940832, 115955), (0, 1)), ((0, 1), (92763509096913722549520924681319505488, 297475)), ((7430573120344896097160065619502297376, 46702), (0, 1)), ((0, 1), (426015827515591504835747624084796200, 3995)), ((19014663643646330047896816814895120, 238), (0, 1)), ((0, 1), (694735050462700190335000447597819, 12)), ((21484730563871049806754891012467, 1), (0, 1)), ((0, 1), (575940198147244876063044459048, 1)), ((13624644306954537072122042449, 1), (0, 1)), ((0, 1), (288409584793102620701524698, 1)), ((5524069426707557147709103, 1), (0, 1)), ((0, 1), (96610270430863131411184, 1)), ((1554509560456728493244, 1), (0, 1)), ((0, 1), (23160828995899601714, 1)), ((321286257255507895, 1), (0, 1)), ((0, 1), (4169423196183703, 1)), ((50829450243937, 1), (0, 1)), ((0, 1), (584261569385, 1)), ((6352886792, 1), (0, 1)), ((0, 1), (65535525, 1)), ((643083, 1), (0, 1)), ((0, 1), (6017, 1)), ((54, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 1), (0, 1)), ((0, 0), (0, 1))]

theorem cc_check : allWithin 384 (pairUp (ceV (2 ^ 512) 40 xB false) (ceV (2 ^ 512) 40 xB true)) ccSpec = true := by
  decide +kernel

theorem ce_zero (odd : Bool) {n : ℕ} (hn : 40 ≤ n) : ce 40 odd n = 0 := by
  unfold ce
  refine sum_eq_zero (fun j hj => ?_)
  simp at hj
  rw [ξ_supp j n (by omega)]; ring

theorem hyp_encl (n : ℕ) (odd : Bool) {c : ℤ} {r : ℕ} (hm : mem (2 ^ 128) (ce 40 odd n) (c, r)) :
    |(∫ y in Set.Icc (-halfWidth) halfWidth, (basisPoly n).eval y *
        (if odd then Real.sinh (y / 2) else Real.cosh (y / 2))) - halfWidth * cc n * ((c : ℝ) / 2 ^ 128)| ≤
      halfWidth * cc n * ((r : ℝ) / 2 ^ 128 + 1 / 10 ^ 60) := by
  obtain ⟨R, hR, he⟩ := hyp_eq n 40 (by norm_num) odd
  rw [he]
  have hF : 0 ≤ halfWidth * cc n := mul_nonneg halfWidth_pos.le (Real.sqrt_nonneg _)
  unfold mem at hm; push_cast at hm
  rw [← mul_sub, abs_mul, abs_of_nonneg hF]
  apply mul_le_mul_of_nonneg_left _ hF
  have := abs_add_le (ce 40 odd n - (c : ℝ) / 2 ^ 128) R
  have e : ce 40 odd n + R - (c : ℝ) / 2 ^ 128 = (ce 40 odd n - (c : ℝ) / 2 ^ 128) + R := by ring
  rw [e]; linarith [bnd_le]

/-- Membership from the kernel check, for n < 40. -/
theorem ce_mem (n : ℕ) (hn : n < 40) (odd : Bool) :
    mem (2 ^ 128) (ce 40 odd n)
      (if odd then (ccSpec.getD n ((0,0),(0,0))).2 else (ccSpec.getD n ((0,0),(0,0))).1) := by
  have hS : 0 < 2 ^ 512 := by positivity
  have hlen : n < (pairUp (ceV (2 ^ 512) 40 xB false) (ceV (2 ^ 512) 40 xB true)).length := by
    have : (pairUp (ceV (2 ^ 512) 40 xB false) (ceV (2 ^ 512) 40 xB true)).length = 40 := by decide +kernel
    omega
  obtain ⟨w1, w2⟩ := allWithin_get 384 _ _ cc_check n hlen
  rw [pairUp_get] at w1 w2
  have m1 := ceV_mem hS xB_mem 40 false n
  have m2 := ceV_mem hS xB_mem 40 true n
  cases odd
  · exact mem_coarse (p := 128) (sh := 384) m1 w1
  · exact mem_coarse (p := 128) (sh := 384) m2 w2

end RHCcEncl0510

