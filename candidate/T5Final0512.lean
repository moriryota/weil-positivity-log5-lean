import T5Tab0512_E
import T5Tab0512_O

/-! # 0512: T5 — the fixed-width G5c gap, from the Gershgorin certificate. -/

open Finset
open scoped BigOperators

namespace RHT5Final0512
open RHConditionalLog5 RHBall0504 RHBallDot0509 RHBallMisc0512 RHEntryBall0512 RHQForm0512 RHLowBlock0494

namespace PE
open RHT5E0512

lemma a_mem (i j : Fin 32) : mem S128 (A0true false i j) (tget aTab i j) := by
  rw [← aTab_eq, tget_ofFn, RHColDecomp0499.A0true_eq]
  exact entry_mem _ _ (by unfold degree; simp; omega) (by unfold degree; simp; omega)

lemma t_mem (i j : Fin 32) : mem S128 (Attrue false i j) (tget tTab i j) := by
  rw [← tTab_eq, tget_ofFn, RHColDecomp0499.Attrue_eq]
  exact entry_mem _ _ (by unfold degree; simp; omega) (by unfold degree; simp; omega)

lemma b_mem (i j : Fin 32) : mem S128 (Bm false i j) (bB i j) := by
  have e : Bm false i j = ((BQ i j : ℚ) : ℝ) := by
    unfold Bm BQ
    show RHFixedCoordinates.B false i j = _
    simp only [RHFixedCoordinates.B, Bool.false_eq_true, if_false, if_true]
    exact RHBQ0512.even_eq i j
  rw [e]; exact mem_qBall hS _

lemma w_mem (i : Fin 32) : mem S128 (1 / wt false i) (wB i) := by
  have e : 1 / wt false i = ((1 / wq i : ℚ) : ℝ) := by
    unfold wt wq
    simp only [RHConcreteParameters.concrete, RHFixedWeights.shift, Bool.false_eq_true, if_false, if_true]
    push_cast; ring
  rw [e]; exact mem_qBall hS _

lemma ba_mem (p j : Fin 32) : mem S128 (∑ i : Fin 32, Bm false i p * A0true false i j) (tget baTab p j) := by
  rw [← baTab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun i => mem_mulB hS (b_mem i p) (a_mem i j))

lemma t1_mem (p q : Fin 32) :
    mem S128 (∑ j : Fin 32, (∑ i : Fin 32, Bm false i p * A0true false i j) * Bm false j q) (tget t1Tab p q) := by
  rw [← t1Tab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun j => mem_mulB hS (ba_mem p j) (b_mem j q))

lemma g_mem (i p : Fin 32) : mem S128 (G false i p) (tget gTab i p) := by
  rw [← gTab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun j => mem_mulB hS (b_mem j p) (t_mem i j))

lemma t2_mem (p q : Fin 32) :
    mem S128 (∑ i : Fin 32, G false i p * G false i q * (1 / wt false i)) (tget t2Tab p q) := by
  rw [← t2Tab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun i => mem_mulB hS (mem_mulB hS (g_mem i p) (g_mem i q)) (w_mem i))

lemma M_mem (p q : Fin 32) : mem S128 (Mq false p q) (mB p q) := by
  have e : Mq false p q = (∑ j : Fin 32, (∑ i : Fin 32, Bm false i p * A0true false i j) * Bm false j q) -
      ∑ i : Fin 32, G false i p * G false i q * (1 / wt false i) := by
    unfold Mq
    congr 1
    · rw [sum_comm]; exact sum_congr rfl (fun j _ => by rw [sum_mul]; exact sum_congr rfl (fun i _ => by ring))
    · exact sum_congr rfl (fun i _ => by ring)
  rw [e]; exact mem_sub (t1_mem p q) (t2_mem p q)

theorem row (p : Fin 32) : 1 - (1 / 1000 : ℝ) ≤ Mq false p p - (1/2) * ∑ q ∈ univ.erase p, (|Mq false p q| + |Mq false q p|) := by
  have hr := rows_ok p
  unfold rowOK at hr
  have hr' := of_decide_eq_true hr
  have hS' : (0:ℝ) < S128 := by exact_mod_cast hS
  have hlo : (((mB p p).1 - (mB p p).2 : ℤ) : ℝ) / S128 ≤ Mq false p p := by
    have := M_mem p p; unfold mem at this; rw [abs_le] at this; push_cast; rw [sub_div]; linarith [this.1]
  have hup : ∀ q r : Fin 32, |Mq false q r| ≤ (((mB q r).1.natAbs + (mB q r).2 : ℕ) : ℝ) / S128 := by
    intro q r
    have := M_mem q r; unfold mem at this
    have h2 := abs_sub_abs_le_abs_sub (Mq false q r) (((mB q r).1 : ℝ) / S128)
    have h3 : |((mB q r).1 : ℝ) / S128| = ((mB q r).1.natAbs : ℝ) / S128 := by
      rw [abs_div, abs_of_pos hS']; congr 1
      have hz : (((mB q r).1.natAbs : ℤ) : ℝ) = |((mB q r).1 : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
      rw [← hz]; rfl
    push_cast; rw [add_div]; linarith
  have hsum : ∑ q ∈ univ.erase p, (|Mq false p q| + |Mq false q p|) ≤
      ∑ q ∈ univ.erase p, ((((mB p q).1.natAbs + (mB p q).2 : ℕ) : ℝ) + (((mB q p).1.natAbs + (mB q p).2 : ℕ) : ℝ)) / S128 := by
    refine sum_le_sum (fun q _ => ?_)
    rw [add_div]; exact add_le_add (hup p q) (hup q p)
  have hr'' := (Rat.cast_le (K := ℝ)).mpr hr'
  push_cast at hr'' hlo hsum
  linarith

end PE

namespace PO
open RHT5O0512

lemma a_mem (i j : Fin 32) : mem S128 (A0true true i j) (tget aTab i j) := by
  rw [← aTab_eq, tget_ofFn, RHColDecomp0499.A0true_eq]
  exact entry_mem _ _ (by unfold degree; simp; omega) (by unfold degree; simp; omega)

lemma t_mem (i j : Fin 32) : mem S128 (Attrue true i j) (tget tTab i j) := by
  rw [← tTab_eq, tget_ofFn, RHColDecomp0499.Attrue_eq]
  exact entry_mem _ _ (by unfold degree; simp; omega) (by unfold degree; simp; omega)

lemma b_mem (i j : Fin 32) : mem S128 (Bm true i j) (bB i j) := by
  have e : Bm true i j = ((BQ i j : ℚ) : ℝ) := by
    unfold Bm BQ
    show RHFixedCoordinates.B true i j = _
    simp only [RHFixedCoordinates.B, Bool.false_eq_true, if_false, if_true]
    exact RHBQ0512.odd_eq i j
  rw [e]; exact mem_qBall hS _

lemma w_mem (i : Fin 32) : mem S128 (1 / wt true i) (wB i) := by
  have e : 1 / wt true i = ((1 / wq i : ℚ) : ℝ) := by
    unfold wt wq
    simp only [RHConcreteParameters.concrete, RHFixedWeights.shift, Bool.false_eq_true, if_false, if_true]
    push_cast; ring
  rw [e]; exact mem_qBall hS _

lemma ba_mem (p j : Fin 32) : mem S128 (∑ i : Fin 32, Bm true i p * A0true true i j) (tget baTab p j) := by
  rw [← baTab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun i => mem_mulB hS (b_mem i p) (a_mem i j))

lemma t1_mem (p q : Fin 32) :
    mem S128 (∑ j : Fin 32, (∑ i : Fin 32, Bm true i p * A0true true i j) * Bm true j q) (tget t1Tab p q) := by
  rw [← t1Tab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun j => mem_mulB hS (ba_mem p j) (b_mem j q))

lemma g_mem (i p : Fin 32) : mem S128 (G true i p) (tget gTab i p) := by
  rw [← gTab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun j => mem_mulB hS (b_mem j p) (t_mem i j))

lemma t2_mem (p q : Fin 32) :
    mem S128 (∑ i : Fin 32, G true i p * G true i q * (1 / wt true i)) (tget t2Tab p q) := by
  rw [← t2Tab_eq, tget_ofFn]
  exact mem_bsum hS _ _ (fun i => mem_mulB hS (mem_mulB hS (g_mem i p) (g_mem i q)) (w_mem i))

lemma M_mem (p q : Fin 32) : mem S128 (Mq true p q) (mB p q) := by
  have e : Mq true p q = (∑ j : Fin 32, (∑ i : Fin 32, Bm true i p * A0true true i j) * Bm true j q) -
      ∑ i : Fin 32, G true i p * G true i q * (1 / wt true i) := by
    unfold Mq
    congr 1
    · rw [sum_comm]; exact sum_congr rfl (fun j _ => by rw [sum_mul]; exact sum_congr rfl (fun i _ => by ring))
    · exact sum_congr rfl (fun i _ => by ring)
  rw [e]; exact mem_sub (t1_mem p q) (t2_mem p q)

theorem row (p : Fin 32) : 1 - (1 / 1000 : ℝ) ≤ Mq true p p - (1/2) * ∑ q ∈ univ.erase p, (|Mq true p q| + |Mq true q p|) := by
  have hr := rows_ok p
  unfold rowOK at hr
  have hr' := of_decide_eq_true hr
  have hS' : (0:ℝ) < S128 := by exact_mod_cast hS
  have hlo : (((mB p p).1 - (mB p p).2 : ℤ) : ℝ) / S128 ≤ Mq true p p := by
    have := M_mem p p; unfold mem at this; rw [abs_le] at this; push_cast; rw [sub_div]; linarith [this.1]
  have hup : ∀ q r : Fin 32, |Mq true q r| ≤ (((mB q r).1.natAbs + (mB q r).2 : ℕ) : ℝ) / S128 := by
    intro q r
    have := M_mem q r; unfold mem at this
    have h2 := abs_sub_abs_le_abs_sub (Mq true q r) (((mB q r).1 : ℝ) / S128)
    have h3 : |((mB q r).1 : ℝ) / S128| = ((mB q r).1.natAbs : ℝ) / S128 := by
      rw [abs_div, abs_of_pos hS']; congr 1
      have hz : (((mB q r).1.natAbs : ℤ) : ℝ) = |((mB q r).1 : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
      rw [← hz]; rfl
    push_cast; rw [add_div]; linarith
  have hsum : ∑ q ∈ univ.erase p, (|Mq true p q| + |Mq true q p|) ≤
      ∑ q ∈ univ.erase p, ((((mB p q).1.natAbs + (mB p q).2 : ℕ) : ℝ) + (((mB q p).1.natAbs + (mB q p).2 : ℕ) : ℝ)) / S128 := by
    refine sum_le_sum (fun q _ => ?_)
    rw [add_div]; exact add_le_add (hup p q) (hup q p)
  have hr'' := (Rat.cast_le (K := ℝ)).mpr hr'
  push_cast at hr'' hlo hsum
  linarith

end PO

/-- Caps: η = 1/1000, τ = 99/100 for both parities. -/
noncomputable def capsNew : RHCaps0494.Caps where
  eta := fun _ => 1 / 1000
  tau := fun _ => 99 / 100
  margin := by intro o; cases o <;> norm_num

theorem G5c_concrete : RHCaps0494.G5c RHConcreteParameters.concrete capsNew := by
  apply G5c_of_rows capsNew
  intro o p
  cases o
  · simpa [capsNew] using PE.row p
  · simpa [capsNew] using PO.row p

end RHT5Final0512

