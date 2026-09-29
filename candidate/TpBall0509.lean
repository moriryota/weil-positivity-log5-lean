import BallDot0509
import Prod0508
import TpA0508

/-! # 0509: ball algorithm for the Tp sums

* `vseq`: `(V n k, V n (k+1))` via the three-term recurrence (`vX`, `vsmul`, `vsub`);
* `Wb`: `Wq_l = 2/(2l+1) Σ_{i<M} gq_i β(0,i)_l` from rational coefficients `gq`;
* `tloop`: for each `k`, the pair `(V n k 0, Σ_{l≥1} V_l μ_l + Σ_l V_l Wq_l)` as balls. -/

open Finset
open scoped BigOperators

namespace RHTpBall0509
open RHBall0504 RHBallVec0504 RHBallDot0509 RHSparse0504 RHIter0505 RHProd0508 RHTpA0508

def Vnext (k : ℕ) (b1 b0 : List Ball) : List Ball :=
  vsub (vsmul (2 * (k : ℤ) + 3) (k + 2) (vX b1)) (vsmul ((k : ℤ) + 1) (k + 2) b0)

lemma vecMem_Vnext {S : ℕ} (hS : 0 < S) (n k : ℕ) {b1 b0 : List Ball}
    (h1 : VecMem S (V n (k + 1)) b1) (h0 : VecMem S (V n k) b0) :
    VecMem S (V n (k + 2)) (Vnext k b1 b0) := by
  have t1 := vecMem_vsmul hS (2 * (k : ℤ) + 3) (d := k + 2) (by omega) (vecMem_vX hS h1)
  have t0 := vecMem_vsmul hS ((k : ℤ) + 1) (d := k + 2) (by omega) h0
  have t := vecMem_vsub t1 t0
  have e : V n (k + 2) = fun l => XS (V n (k + 1)) l * ((2 * (k : ℤ) + 3 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ) -
      V n k l * (((k : ℤ) + 1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by
    funext l; simp only [V]; push_cast; ring
  rw [e]; exact t

/-- Weights `μ_l` for `l ≥ 1`, weight 0 at `l = 0`. -/
def muW : ℕ → ℤ × ℕ
  | 0 => (0, 1)
  | m + 1 => (if m % 2 = 0 then 2 else -2, (m + 1) * (m + 2))

lemma muW_den (l : ℕ) : 0 < (muW l).2 := by cases l <;> simp [muW] <;> positivity

noncomputable def muR' (l : ℕ) : ℝ := if l = 0 then 0 else muR l

lemma muW_val (l : ℕ) : ((muW l).1 : ℝ) / (muW l).2 = muR' l := by
  cases l with
  | zero => simp [muW, muR']
  | succ m =>
      simp only [muW, muR', muR, if_neg (Nat.succ_ne_zero m)]
      rcases Nat.even_or_odd m with he | ho
      · rw [if_pos (Nat.even_iff.mp he), pow_add, he.neg_one_pow]; push_cast; ring
      · rw [if_neg (by rw [Nat.odd_iff.mp ho]; omega), pow_add, ho.neg_one_pow]; push_cast; ring

/-- `W` accumulation over `i < M` with `β(0,i)` iterates. -/
def wloop (gq : List (ℤ × ℕ)) : ℕ → ℕ → List Ball → List Ball → List Ball
  | 0, _, _, acc => acc
  | c + 1, i, b, acc => wloop gq c (i + 1) (vadd b (vX b))
      (vadd acc (vsmul (gq.getD i (0, 1)).1 (gq.getD i (0, 1)).2 b))

noncomputable def gqv (gq : List (ℤ × ℕ)) (i : ℕ) : ℝ := ((gq.getD i (0, 1)).1 : ℝ) / (gq.getD i (0, 1)).2

lemma wloop_mem {S : ℕ} (hS : 0 < S) (gq : List (ℤ × ℕ)) (hg : ∀ i, 0 < (gq.getD i (0, 1)).2) :
    ∀ (c i : ℕ) (b acc : List Ball) (A : ℕ → ℝ), VecMem S (β 0 i) b → VecMem S A acc →
      VecMem S (fun l => A l + ∑ j ∈ range c, gqv gq (i + j) * β 0 (i + j) l) (wloop gq c i b acc)
  | 0, i, b, acc, A, _, hA => by simpa [wloop] using hA
  | c + 1, i, b, acc, A, hb, hA => by
      have hb' : VecMem S (β 0 (i + 1)) (vadd b (vX b)) := vecMem_vadd hb (vecMem_vX hS hb)
      have hacc := vecMem_vadd hA (vecMem_vsmul hS (gq.getD i (0, 1)).1 (hg i) hb)
      have ih := wloop_mem hS gq hg c (i + 1) _ _ _ hb' hacc
      simp only [wloop]
      convert ih using 2 with l
      have e : ∑ j ∈ range c, gqv gq (i + (j + 1)) * β 0 (i + (j + 1)) l =
          ∑ j ∈ range c, gqv gq (i + 1 + j) * β 0 (i + 1 + j) l :=
        sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by ring])
      rw [sum_range_succ', e]
      simp only [gqv, add_zero]
      ring

def Wb (S M : ℕ) (gq : List (ℤ × ℕ)) : List Ball :=
  mapI (fun l b => smul 2 (2 * l + 1) b) 0 (wloop gq M 0 (vunit S 0) [])

noncomputable def WqR (M : ℕ) (gq : List (ℤ × ℕ)) (l : ℕ) : ℝ :=
  2 / (2 * l + 1) * ∑ i ∈ range M, gqv gq i * β 0 i l

lemma Wb_mem {S : ℕ} (hS : 0 < S) (M : ℕ) (gq : List (ℤ × ℕ)) (hg : ∀ i, 0 < (gq.getD i (0, 1)).2) :
    VecMem S (WqR M gq) (Wb S M gq) := by
  have h0 : VecMem S (fun _ => (0 : ℝ)) ([] : List Ball) := fun l => by simp [gz, mem]
  have hw := wloop_mem hS gq hg M 0 (vunit S 0) [] (fun _ => 0) (vecMem_vunit hS 0) h0
  refine vecMem_mapI hS _ hw (fun l hm => ?_) (fun l hl => ?_)
  · have := mem_smul hS 2 (d := 2 * l + 1) (by omega) hm
    convert this using 1
    unfold WqR; simp only [zero_add]; push_cast; ring
  · unfold WqR; simp only [zero_add] at hl; rw [hl, mul_zero]

/-- Per-`k` output: `(V n k` ball at 0, `Σ_{l≥1} V_l μ_l + Σ_l V_l Wq_l` ball`)`. -/
def tloop (S : ℕ) (W : List Ball) : ℕ → ℕ → List Ball → List Ball → List (Ball × Ball)
  | 0, _, _, _ => []
  | c + 1, k, b0, b1 => (gz b0 0, add (wsum muW 0 b0) (dotB S b0 W)) :: tloop S W c (k + 1) b1 (Vnext k b1 b0)

def tpRun (S n M : ℕ) (gq : List (ℤ × ℕ)) (K : ℕ) : List (Ball × Ball) :=
  tloop S (Wb S M gq) K 0 (vunit S n) (vX (vunit S n))

noncomputable def TS (n M : ℕ) (gq : List (ℤ × ℕ)) (k : ℕ) (N : ℕ) : ℝ :=
  ∑ l ∈ range N, V n k l * muR' l + ∑ l ∈ range N, V n k l * WqR M gq l

lemma sum_supp {c w : ℕ → ℝ} {A B : ℕ} (hA : ∀ l, A ≤ l → c l = 0) (hB : ∀ l, B ≤ l → c l = 0) :
    ∑ l ∈ range A, c l * w l = ∑ l ∈ range B, c l * w l := by
  have key : ∀ C, A ≤ C → ∑ l ∈ range A, c l * w l = ∑ l ∈ range C, c l * w l := fun C h =>
    sum_subset (range_subset_range.mpr h) (fun l _ hl => by simp at hl; rw [hA l hl, zero_mul])
  have key' : ∀ C, B ≤ C → ∑ l ∈ range B, c l * w l = ∑ l ∈ range C, c l * w l := fun C h =>
    sum_subset (range_subset_range.mpr h) (fun l _ hl => by simp at hl; rw [hB l hl, zero_mul])
  rw [key (A + B) (by omega), key' (A + B) (by omega)]

theorem tloop_mem {S : ℕ} (hS : 0 < S) (n M : ℕ) (gq : List (ℤ × ℕ)) (hg : ∀ i, 0 < (gq.getD i (0, 1)).2) :
    ∀ (c k : ℕ) (b0 b1 : List Ball), VecMem S (V n k) b0 → VecMem S (V n (k + 1)) b1 →
      ∀ j < c, mem S (V n (k + j) 0) ((tloop S (Wb S M gq) c k b0 b1).getD j ((0,0),(0,0))).1 ∧
        mem S (TS n M gq (k + j) (n + (k + j) + 1)) ((tloop S (Wb S M gq) c k b0 b1).getD j ((0,0),(0,0))).2
  | 0, k, b0, b1, _, _, j, hj => absurd hj (by omega)
  | c + 1, k, b0, b1, h0, h1, 0, _ => by
      simp only [tloop, List.getD_cons_zero, add_zero]
      refine ⟨h0 0, ?_⟩
      have hW := Wb_mem hS M gq hg
      have hs := mem_wsum hS muW muW_den 0 b0 (V n k) h0
      have hd := mem_dotB hS b0 (Wb S M gq) (V n k) (WqR M gq) h0 hW
      have hlen : ∀ l, b0.length ≤ l → V n k l = 0 := fun l hl => zero_of_len hS h0 hl
      have e1 : ∑ l ∈ range b0.length, V n k l * ((muW (0 + l)).1 : ℝ) / ((muW (0 + l)).2 : ℝ) =
          ∑ l ∈ range (n + k + 1), V n k l * muR' l := by
        have : ∑ l ∈ range b0.length, V n k l * ((muW (0 + l)).1 : ℝ) / ((muW (0 + l)).2 : ℝ) =
            ∑ l ∈ range b0.length, V n k l * muR' l :=
          sum_congr rfl (fun l _ => by rw [zero_add, mul_div_assoc, muW_val])
        rw [this]; exact sum_supp hlen (V_supp n k)
      have e2 : ∑ l ∈ range (min b0.length (Wb S M gq).length), V n k l * WqR M gq l =
          ∑ l ∈ range (n + k + 1), V n k l * WqR M gq l := by
        rw [← sum_supp (w := WqR M gq) hlen (V_supp n k)]
        apply sum_subset (range_subset_range.mpr (min_le_left _ _))
        intro l hl hl'
        simp at hl hl'
        rw [(zero_of_len hS hW (hl' hl)), mul_zero]
      rw [e1] at hs; rw [e2] at hd
      exact mem_add hs hd
  | c + 1, k, b0, b1, h0, h1, j + 1, hj => by
      simp only [tloop, List.getD_cons_succ]
      have ih := tloop_mem hS n M gq hg c (k + 1) b1 (Vnext k b1 b0) h1 (vecMem_Vnext hS n k h1 h0) j (by omega)
      rw [show k + 1 + j = k + (j + 1) by ring] at ih
      exact ih

theorem tpRun_mem {S : ℕ} (hS : 0 < S) (n M : ℕ) (gq : List (ℤ × ℕ)) (hg : ∀ i, 0 < (gq.getD i (0, 1)).2)
    (K k : ℕ) (hk : k < K) :
    mem S (V n k 0) ((tpRun S n M gq K).getD k ((0,0),(0,0))).1 ∧
      mem S (TS n M gq k (n + k + 1)) ((tpRun S n M gq K).getD k ((0,0),(0,0))).2 := by
  have h0 : VecMem S (V n 0) (vunit S n) := vecMem_vunit hS n
  have h1 : VecMem S (V n 1) (vX (vunit S n)) := vecMem_vX hS (vecMem_vunit hS n)
  have := tloop_mem hS n M gq hg K 0 (vunit S n) (vX (vunit S n)) h0 h1 k hk
  simpa [tpRun] using this

end RHTpBall0509

