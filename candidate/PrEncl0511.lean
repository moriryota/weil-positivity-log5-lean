import PrBall0511
import PrSum0511
import Coarse0509

/-! # 0511: rigorous enclosure of `Pr(n,k)`

`T n k = Σ_{m∈{2,3,4}} w_m α_m D_m(n,k)`, `Pr n k = (1+(−1)^{n+k}) L c_n c_k T n k`;
`prT (2^512) n k ⊇ T n k` (balls for `σ_m = log m / L`, `α_m = (2−σ_m)/2`, `w_m`).
 -/

open Finset
open scoped BigOperators

namespace RHPrEncl0511
open RHConditionalLog5 RHLog5Bridge RHBall0504 RHBallVec0504 RHBallDot0509 RHPrAff0511 RHPrBall0511 RHPrRed0511
  RHPrSum0511 RHRpExact0506 RHEntry00Bounds0495 RHCoarse0509

lemma mem_of_bounds {S : ℕ} (hS : 0 < S) {x : ℝ} {lo hi : ℚ} {m : ℤ} {e : ℕ} (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi)
    (c1 : (m : ℚ) / S - (e : ℚ) / S ≤ lo) (c2 : hi ≤ (m : ℚ) / S + (e : ℚ) / S) : mem S x (m, e) := by
  have c1' := (Rat.cast_le (K := ℝ)).mpr c1
  have c2' := (Rat.cast_le (K := ℝ)).mpr c2
  push_cast at c1' c2'
  unfold mem; simp only; rw [abs_le]; constructor <;> linarith

def S512 : ℕ := 2 ^ 512
def sB2 : Ball := (11548857141153645566405316090144528040652565907076733801380529688304802440197105677528802420736228904918643610216516618861295535381258246129828497137838594, 1191859366075723082005274251328715257335667465940897849)
def sB3 : Ball := (18304505494914264677112793017453390569890755984113301896749904846337295743646668144661190105166523040235175356833586229385527461431784101470107941939371514, 1401735382465303258740257232315824190100912634787022239)
def sB4 : Ball := (23097714282307291132810632180289056081305131814153467602761059376609604880394211355057604841472457809837287220433033237722591070762516492259656994275677187, 2383718732151446164010548502657430514671334931881795697)
def wB2 : Ball := (6571556454694197541019802844691583585770733739442111335961268141081550021963140572419549736579653687700101571855971184156338411632306983253186601376052545, 70637720200868353387623733929893650880510619427947097025447284700001671924843450658456610833554617191313004608462168805365)
def wB3 : Ball := (8504359393828526284933607988663080409182584676101517993122591717513404291386502371439734336734709896574381135776879828815123185300029894316802503945864368, 63254978514536898306500801207502314343346168982977844841591173115534273384980344235544367972319512169626437110262933475862)
def wB4 : Ball := (4646792132064493950692220330326530046587753977397832781338111720864985485780029539044354323873261320752517783149469525505297654192622651074673642776677747, 33519519824856492748935062495514615318698414551480983444308903609304410075183867442004685745417258569225079645466215127136)

lemma hS : 0 < S512 := by unfold S512; positivity

lemma pos5 : 0 < Real.log 5 := Real.log_pos (by norm_num)

lemma sig_eq (m : ℝ) : Real.log m / halfWidth = 2 * Real.log m / Real.log 5 := by
  unfold halfWidth; field_simp

lemma div_bounds {a b : ℝ} {al ah bl bh : ℚ} (ha : (al : ℝ) ≤ a ∧ a ≤ ah) (hb : (bl : ℝ) ≤ b ∧ b ≤ bh)
    (hal : 0 ≤ al) (hbl : 0 < bl) :
    ((al / bh : ℚ) : ℝ) ≤ a / b ∧ a / b ≤ ((ah / bl : ℚ) : ℝ) := by
  have hbl' : (0:ℝ) < bl := by exact_mod_cast hbl
  have hal' : (0:ℝ) ≤ al := by exact_mod_cast hal
  have hb0 : 0 < b := lt_of_lt_of_le hbl' hb.1
  have hbh : (0:ℝ) < bh := lt_of_lt_of_le hb0 hb.2
  push_cast
  constructor
  · calc (al : ℝ) / bh ≤ a / bh := div_le_div_of_nonneg_right ha.1 hbh.le
      _ ≤ a / b := div_le_div_of_nonneg_left (hal'.trans ha.1) hb0 hb.2
  · calc a / b ≤ ah / b := div_le_div_of_nonneg_right ha.2 hb0.le
      _ ≤ ah / bl := div_le_div_of_nonneg_left ((hal'.trans ha.1).trans ha.2) hbl' hb.1

lemma two_log (lo hi : ℚ) (h : (lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ hi) (k : ℚ) (hk : 0 ≤ k) :
    ((k * lo : ℚ) : ℝ) ≤ k * Real.log 2 ∧ k * Real.log 2 ≤ ((k * hi : ℚ) : ℝ) := by
  have hk' : (0:ℝ) ≤ k := by exact_mod_cast hk
  push_cast; exact ⟨mul_le_mul_of_nonneg_left h.1 hk', mul_le_mul_of_nonneg_left h.2 hk'⟩

lemma sig2_mem : mem S512 (Real.log 2 / halfWidth) sB2 := by
  rw [sig_eq]
  have h := div_bounds (two_log Trial0455.lo Trial0455.hi Trial0455.log2_bounds 2 (by norm_num)) Trial0456.log5_bounds (by decide +kernel) (by decide +kernel)
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

lemma sig3_mem : mem S512 (Real.log 3 / halfWidth) sB3 := by
  rw [sig_eq]
  have h3 : ((2 * RHConstants0467.log3Lo : ℚ) : ℝ) ≤ 2 * Real.log 3 ∧ 2 * Real.log 3 ≤ ((2 * RHConstants0467.log3Hi : ℚ) : ℝ) := by
    push_cast; constructor <;> linarith [RHConstants0467.log3_bounds.1, RHConstants0467.log3_bounds.2]
  have h := div_bounds h3 Trial0456.log5_bounds (by decide +kernel) (by decide +kernel)
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

lemma sig4_mem : mem S512 (Real.log 4 / halfWidth) sB4 := by
  rw [sig_eq, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have h4 : ((4 * Trial0455.lo : ℚ) : ℝ) ≤ 2 * ((2 : ℕ) * Real.log 2) ∧ 2 * ((2 : ℕ) * Real.log 2) ≤ ((4 * Trial0455.hi : ℚ) : ℝ) := by
    push_cast; constructor <;> linarith [Trial0455.log2_bounds.1, Trial0455.log2_bounds.2]
  have h := div_bounds h4 Trial0456.log5_bounds (by decide +kernel) (by decide +kernel)
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

lemma w2_mem : mem S512 w2 wB2 := by
  have h := div_bounds b_l2 b_q2 (by decide +kernel) (by decide +kernel)
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

lemma w3_mem : mem S512 w3 wB3 := by
  have h := div_bounds b_l3 b_q3 (by decide +kernel) (by decide +kernel)
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

lemma w4_mem : mem S512 w4 wB4 := by
  have h : ((l2L / 2 : ℚ) : ℝ) ≤ w4 ∧ w4 ≤ ((l2H / 2 : ℚ) : ℝ) := by
    unfold w4; push_cast; constructor <;> linarith [b_l2.1, b_l2.2]
  exact mem_of_bounds hS h.1 h.2 (by unfold S512; decide +kernel) (by unfold S512; decide +kernel)

def aOf (sB : Ball) : Ball := sub ((S512 : ℤ), 0) (smul 1 2 sB)
def g1Of (sB : Ball) : Ball := neg (smul 1 2 sB)
def g2Of (sB : Ball) : Ball := smul 1 2 sB

lemma aOf_mem {σ : ℝ} {sB : Ball} (h : mem S512 σ sB) : mem S512 ((2 - σ) / 2) (aOf sB) := by
  have h1 : mem S512 (1 : ℝ) ((S512 : ℤ), 0) := by
    have hpos : (0:ℝ) < S512 := by exact_mod_cast hS
    unfold mem; simp only
    rw [Int.cast_natCast, div_self hpos.ne', sub_self, abs_zero, Nat.cast_zero, zero_div]
  have h2 := mem_smul hS 1 (d := 2) (by norm_num) h
  have := mem_sub h1 h2
  convert this using 1
  · push_cast; ring
  · rfl
lemma g1Of_mem {σ : ℝ} {sB : Ball} (h : mem S512 σ sB) : mem S512 (-(σ) / 2) (g1Of sB) := by
  have := mem_neg (mem_smul hS 1 (d := 2) (by norm_num) h)
  convert this using 1
  · push_cast; ring
  · rfl
lemma g2Of_mem {σ : ℝ} {sB : Ball} (h : mem S512 σ sB) : mem S512 (σ / 2) (g2Of sB) := by
  have := mem_smul hS 1 (d := 2) (by norm_num) h
  convert this using 1
  · push_cast; ring
  · rfl

noncomputable def α_ (m : ℝ) : ℝ := (2 - Real.log m / halfWidth) / 2
noncomputable def D (m : ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ range (n + 1), Af (α_ m) (-(Real.log m / halfWidth) / 2) n j * Af (α_ m) (Real.log m / halfWidth / 2) k j *
    (2 / (2 * j + 1))
noncomputable def T (n k : ℕ) : ℝ := w2 * α_ 2 * D 2 n k + w3 * α_ 3 * D 3 n k + w4 * α_ 4 * D 4 n k

theorem Pr_T (n k : ℕ) : RHColDecomp0499.Pr n k = (1 + (-1) ^ (n + k)) * (halfWidth * cc n * cc k * T n k) := by
  have hL := halfWidth_pos
  have h5 : 2 * halfWidth = Real.log 5 := by unfold halfWidth; ring
  have lt : ∀ m : ℝ, 1 ≤ m → m < 5 → 0 ≤ Real.log m ∧ Real.log m < 2 * halfWidth := by
    intro m h1 h2; rw [h5]; exact ⟨Real.log_nonneg h1, Real.log_lt_log (by linarith) h2⟩
  rw [Pr_eq, Jm_eq n k (lt 2 (by norm_num) (by norm_num)).1 (lt 2 (by norm_num) (by norm_num)).2,
    Jm_eq n k (lt 3 (by norm_num) (by norm_num)).1 (lt 3 (by norm_num) (by norm_num)).2,
    Jm_eq n k (lt 4 (by norm_num) (by norm_num)).1 (lt 4 (by norm_num) (by norm_num)).2]
  unfold T D α_; ring

def rowB (sB wB : Ball) (N K : ℕ) : List (List Ball) × List (List Ball) × Ball :=
  (afAll S512 (aOf sB) (g1Of sB) N, afAll S512 (aOf sB) (g2Of sB) K, mulB S512 wB (aOf sB))

def prT (R2 R3 R4 : List (List Ball) × List (List Ball) × Ball) (n k : ℕ) : Ball :=
  add (add (mulB S512 R2.2.2 (dB S512 (R2.1.getD n []) (R2.2.1.getD k [])))
    (mulB S512 R3.2.2 (dB S512 (R3.1.getD n []) (R3.2.1.getD k []))))
    (mulB S512 R4.2.2 (dB S512 (R4.1.getD n []) (R4.2.1.getD k [])))

def R2 : List (List Ball) × List (List Ball) × Ball := rowB sB2 wB2 64 128
def R3 : List (List Ball) × List (List Ball) × Ball := rowB sB3 wB3 64 128
def R4 : List (List Ball) × List (List Ball) × Ball := rowB sB4 wB4 64 128

lemma comp_mem {m : ℝ} {sB wB : Ball} {w : ℝ} (hs : mem S512 (Real.log m / halfWidth) sB) (hw : mem S512 w wB)
    (n k : ℕ) (hn : n < 64) (hk : k < 128) :
    mem S512 (w * α_ m * D m n k) (mulB S512 (rowB sB wB 64 128).2.2
      (dB S512 ((rowB sB wB 64 128).1.getD n []) ((rowB sB wB 64 128).2.1.getD k []))) := by
  have ha := aOf_mem hs
  have hA := afAll_mem hS ha (g1Of_mem hs) 64 n hn
  have hB := afAll_mem hS ha (g2Of_mem hs) 128 k hk
  have hd := dB_mem hS hA hB (n + 1) (fun j hj => Af_supp _ _ n j hj)
  have hwa := mem_mulB hS hw ha
  have := mem_mulB hS hwa hd
  unfold D α_; simpa [rowB] using this

theorem prT_mem (n k : ℕ) (hn : n < 64) (hk : k < 128) : mem S512 (T n k) (prT R2 R3 R4 n k) := by
  unfold T prT
  exact mem_add (mem_add (comp_mem sig2_mem w2_mem n k hn hk) (comp_mem sig3_mem w3_mem n k hn hk))
    (comp_mem sig4_mem w4_mem n k hn hk)

theorem Pr_encl (n k : ℕ) {c : ℤ} {r : ℕ} (hm : mem (2 ^ 128) (T n k) (c, r)) :
    |RHColDecomp0499.Pr n k - (1 + (-1) ^ (n + k)) * (halfWidth * cc n * cc k * ((c : ℝ) / 2 ^ 128))| ≤
      |1 + (-1) ^ (n + k)| * (halfWidth * cc n * cc k * ((r : ℝ) / 2 ^ 128)) := by
  rw [Pr_T, ← mul_sub, ← mul_sub, abs_mul, abs_mul]
  have hF : 0 ≤ halfWidth * cc n * cc k :=
    mul_nonneg (mul_nonneg halfWidth_pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hF]
  simp only [mem, Nat.cast_pow, Nat.cast_ofNat] at hm
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hF) (abs_nonneg _)

end RHPrEncl0511

