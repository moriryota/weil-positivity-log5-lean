import MpTab0515
import PiBounds0466
import BallDot0509

/-! # 0515: base rows `ν_l`, `κ_l` as balls (scale `2^256`) and their enclosure lemmas

`L2B ∋ log 2`, `PiB ∋ π` (100-digit bounds), `hB n ∋ H_n`, `nuB l ∋ ν_l`, `kaB l ∋ κ_l`
(closed forms from 0514). -/

namespace RHBaseNK0515
open RHBall0504 RHBallVec0504 RHBallDot0509 RHRec2D0515 RHTabCore0515 RHLeg0503 RHBallMisc0512

def L2B : Ball := (80260960185991308862233904206310070533990667611589946606122867505419956976171, 2)
def PiB : Ball := (363771576891766324280234942777729862653393377328392429958772151117938894466185, 2)
def Pi2B : Ball := mulB (2 ^ 256) PiB PiB

def hB : ℕ → Ball
  | 0 => (0, 0)
  | n + 1 => add (hB n) (ratBall (2 ^ 256) 1 (n + 1))

def nu0B : Ball := add (sub (smul 2 1 (mulB (2 ^ 256) L2B L2B)) (smul 4 1 L2B)) (ratBall (2 ^ 256) 4 1)

def nuB (l : ℕ) : Ball :=
  if l = 0 then nu0B else
    add (smul (if l % 2 = 1 then 4 else -4) (l * (l + 1)) L2B)
      (smul (if l % 2 = 1 then -4 else 4) (l * (l + 1)) (add (hB (l - 1)) (hB (l + 1))))

def kaB (l : ℕ) : Ball :=
  if l = 0 then sub nu0B (smul 1 3 Pi2B) else
    if l % 2 = 1 then (0, 0) else
      add (smul (-4) (l * (l + 1)) L2B) (smul 2 (l * (l + 1)) (RHMpTab0515.muB l))

def nuBase : List Ball := (List.range 127).map nuB
def kaBase : List Ball := (List.range 127).map kaB

lemma hS : 0 < (2 : ℕ) ^ 256 := by positivity

lemma mem_L2B : mem (2 ^ 256) (Real.log 2) L2B := by
  obtain ⟨h1, h2⟩ := Trial0455.log2_bounds
  have q1 : ((L2B.1 : ℚ) - L2B.2) / (2 ^ 256 : ℕ) ≤ Trial0455.lo := by decide +kernel
  have q2 : Trial0455.hi ≤ ((L2B.1 : ℚ) + L2B.2) / (2 ^ 256 : ℕ) := by decide +kernel
  have r1 : ((((L2B.1 : ℚ) - L2B.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) ≤ ((Trial0455.lo : ℚ) : ℝ) := by exact_mod_cast q1
  have r2 : ((Trial0455.hi : ℚ) : ℝ) ≤ ((((L2B.1 : ℚ) + L2B.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) := by exact_mod_cast q2
  simp only [L2B] at r1 r2 ⊢
  push_cast at r1 r2
  exact mem_of_bounds' hS (by push_cast; linarith) (by push_cast; linarith)

lemma mem_PiB : mem (2 ^ 256) Real.pi PiB := by
  obtain ⟨h1, h2⟩ := RHPi0466.pi_bounds
  have q1 : ((PiB.1 : ℚ) - PiB.2) / (2 ^ 256 : ℕ) ≤ RHPi0466.piLo := by decide +kernel
  have q2 : RHPi0466.piHi ≤ ((PiB.1 : ℚ) + PiB.2) / (2 ^ 256 : ℕ) := by decide +kernel
  have r1 : ((((PiB.1 : ℚ) - PiB.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) ≤ ((RHPi0466.piLo : ℚ) : ℝ) := by
    exact_mod_cast q1
  have r2 : ((RHPi0466.piHi : ℚ) : ℝ) ≤ ((((PiB.1 : ℚ) + PiB.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) := by
    exact_mod_cast q2
  simp only [PiB] at r1 r2 ⊢
  push_cast at r1 r2
  exact mem_of_bounds' hS (by push_cast; linarith) (by push_cast; linarith)

lemma mem_hB : ∀ n, mem (2 ^ 256) (RHNuK0514.H n) (hB n)
  | 0 => by simp only [hB, RHNuK0514.H, Finset.range_zero, Finset.sum_empty]; exact (mem_zero _ hS).mpr rfl
  | n + 1 => by
    rw [RHNuK0514.H_succ]
    have h := mem_add (mem_hB n) (mem_ratBall (S := 2 ^ 256) hS 1 (D := n + 1) (by omega))
    simp only [hB]
    convert h using 2
    push_cast; ring

lemma nu0_val : 2 * Real.log 2 ^ 2 - 4 * Real.log 2 + 4 =
    Real.log 2 * Real.log 2 * ((2:ℤ):ℝ) / ((1:ℕ):ℝ) - Real.log 2 * ((4:ℤ):ℝ) / ((1:ℕ):ℝ) + ((4:ℤ):ℝ) / ((1:ℕ):ℝ) := by
  push_cast; ring

lemma mem_nu0 : mem (2 ^ 256) (2 * Real.log 2 ^ 2 - 4 * Real.log 2 + 4) nu0B := by
  rw [nu0_val]
  exact mem_add (mem_sub (mem_smul hS 2 (by norm_num) (mem_mulB hS mem_L2B mem_L2B))
    (mem_smul hS 4 (by norm_num) mem_L2B)) (mem_ratBall hS 4 (by norm_num))

lemma MwN0 (l : ℕ) : Mw (fun x => Real.log (1 + x) ^ 2) 0 l = ∫ x in (-1:ℝ)..1, Real.log (1 + x) ^ 2 * p l x := by
  unfold Mw; simp only [p_zero, one_mul]

lemma MwK0 (l : ℕ) : Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) 0 l =
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) * Real.log (1 - x) * p l x := by
  unfold Mw; simp only [p_zero, one_mul, mul_assoc]

lemma mem_nuB (l : ℕ) : mem (2 ^ 256) (Mw (fun x => Real.log (1 + x) ^ 2) 0 l) (nuB l) := by
  rw [MwN0]
  cases l with
  | zero => simpa [nuB, RHNu0514.nu_zero] using mem_nu0
  | succ n =>
    rw [RHNuK0514.nu_closed]
    have hD : 0 < (n + 1) * (n + 1 + 1) := by positivity
    simp only [nuB, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    rcases Nat.even_or_odd n with he | ho
    · have hp : (n + 1) % 2 = 1 := by rcases he with ⟨k, hk⟩; omega
      simp only [if_pos hp]
      have h := mem_add (mem_smul hS 4 hD mem_L2B) (mem_smul hS (-4) hD (mem_add (mem_hB n) (mem_hB (n + 1 + 1))))
      convert h using 1
      simp only [RHNuK0514.muC]
      rw [pow_add, he.neg_one_pow]; push_cast; ring
    · have hp : ¬ (n + 1) % 2 = 1 := by rcases ho with ⟨k, hk⟩; omega
      simp only [if_neg hp]
      have h := mem_add (mem_smul hS (-4) hD mem_L2B) (mem_smul hS 4 hD (mem_add (mem_hB n) (mem_hB (n + 1 + 1))))
      convert h using 1
      simp only [RHNuK0514.muC]
      rw [pow_add, ho.neg_one_pow]; push_cast; ring

lemma mem_kaB (l : ℕ) : mem (2 ^ 256) (Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) 0 l) (kaB l) := by
  rw [MwK0]
  cases l with
  | zero =>
    rw [RHDilog0514.kappa_zero]
    have h := mem_sub mem_nu0 (mem_smul hS 1 (d := 3) (by norm_num) (mem_mulB hS mem_PiB mem_PiB))
    rw [show kaB 0 = sub nu0B (smul 1 3 Pi2B) from rfl]
    unfold Pi2B
    convert h using 1
    push_cast; ring
  | succ n =>
    rw [RHNuK0514.kappa_closed]
    simp only [kaB, if_neg (Nat.succ_ne_zero n)]
    rcases Nat.even_or_odd n with he | ho
    · have hp : (n + 1) % 2 = 1 := by rcases he with ⟨k, hk⟩; omega
      simp only [if_pos hp]
      rw [mem_zero _ hS, pow_add, he.neg_one_pow]; ring
    · have hp : ¬ (n + 1) % 2 = 1 := by rcases ho with ⟨k, hk⟩; omega
      simp only [if_neg hp]
      have hD : 0 < (n + 1) * (n + 1 + 1) := by positivity
      have h := mem_add (mem_smul hS (-4) hD mem_L2B) (mem_smul hS 2 hD (RHMpTab0515.mem_muB (n + 1)))
      convert h using 1
      rw [pow_add, ho.neg_one_pow]; push_cast; ring

lemma nuBase_row : RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x) ^ 2) 0) nuBase := by
  intro i hi
  simp only [nuBase, List.length_map, List.length_range] at hi
  have e : gz nuBase i = nuB i := by simp [gz, nuBase, List.getD_eq_getElem?_getD, hi]
  rw [e]; exact mem_nuB i

lemma kaBase_row : RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) 0) kaBase := by
  intro i hi
  simp only [kaBase, List.length_map, List.length_range] at hi
  have e : gz kaBase i = kaB i := by simp [gz, kaBase, List.getD_eq_getElem?_getD, hi]
  rw [e]; exact mem_kaB i

lemma kw_ii : IntervalIntegrable (fun x => Real.log (1 + x) * Real.log (1 - x)) MeasureTheory.volume (-1) 1 := by
  have hb : IntervalIntegrable (fun x => Real.log 2 * (|Real.log (1 + x)| + |Real.log (1 - x)|))
      MeasureTheory.volume (-1) 1 :=
    ((RHLogMoment0508.log1p_ii.norm).add (RHKappa0514.log1m_ii.norm)).const_mul (Real.log 2) |>.congr
      (fun x _ => by simp [Real.norm_eq_abs])
  refine hb.mono_fun ?_ ?_
  · exact ((Real.measurable_log.comp (measurable_const.add measurable_id)).mul
      (Real.measurable_log.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.uIoc_of_le (by norm_num)] at hx
    dsimp only
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hs : 0 ≤ |Real.log (1 + x)| + |Real.log (1 - x)| := by positivity
    rw [abs_of_nonneg (mul_nonneg hl2 hs)]
    rcases le_total x 0 with h0 | h0
    · have hb2 : |Real.log (1 - x)| ≤ Real.log 2 := by
        rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
        exact Real.log_le_log (by linarith) (by linarith [hx.1])
      nlinarith [abs_nonneg (Real.log (1 + x)), abs_nonneg (Real.log (1 - x))]
    · have hb1 : |Real.log (1 + x)| ≤ Real.log 2 := by
        rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
        exact Real.log_le_log (by linarith) (by linarith [hx.2])
      nlinarith [abs_nonneg (Real.log (1 + x)), abs_nonneg (Real.log (1 - x))]

end RHBaseNK0515

