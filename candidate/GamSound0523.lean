import OOSound0523
import Gam0522
import NTab0515
import KTab0515
import GammaThm0516

/-! # 0523: soundness of the γ tables: `gzz gamE ii kk ∋ ∫ φ_{deg ii} φ_{deg kk}` (same for odd). -/

open Finset
open scoped BigOperators

namespace RHGamSound0523
open RHBall0504 RHBallVec0504 RHBallDot0509 RHG6Core0522 RHRec2D0515 RHGam0522 RHConditionalLog5
  RHFSound0523 RHOOSound0523

local notation "S" => (2:ℕ) ^ 256

lemma OO_symm (i k : ℕ) (s t : ℝ) : RHPairInt0516.OO i k s t = RHPairInt0516.OO k i t s := by
  unfold RHPairInt0516.OO; rw [max_comm]; congr 1; funext u; ring

lemma rowlen {T : List (List Ball)} {n : ℕ}
    (h : (List.range 64).all (fun j => decide (n - j ≤ (T.getD j []).length)) = true) :
    ∀ j < 64, n - j ≤ (T.getD j []).length := by
  intro j hj; simpa [hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

lemma tab_entry {T : List (List Ball)} {f : ℕ → ℕ → ℝ} (hT : ∀ j, RowMem S (f j) (T.getD j []))
    (hl : ∀ j < 64, 127 - j ≤ (T.getD j []).length) {i k : ℕ} (hi : i < 64) (hk : k < 64) :
    mem S (f i k) (gzz T i k) := hT i k (by have := hl i hi; omega)

noncomputable def w : ℕ → ℝ
  | 2 => RHPrSum0511.w2
  | 3 => RHPrSum0511.w3
  | _ => RHPrSum0511.w4

lemma wBm_mem (a : ℕ) (ha : a = 2 ∨ a = 3 ∨ a = 4) : mem S (w a) (wBm a) := by
  rcases ha with rfl | rfl | rfl
  · exact RHConst0521.w2_mem
  · exact RHConst0521.w3_mem
  · exact RHConst0521.w4_mem

lemma Fm_mem (a : ℕ) (ha : a = 2 ∨ a = 3 ∨ a = 4) (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.F i k (RHSingDef0516.σ a)) (gzz (Ftab a) i k) := by
  rcases ha with rfl | rfl | rfl
  · exact F2_mem i k hi hk
  · exact F3_mem i k hi hk
  · exact F4_mem i k hi hk

lemma OOb_mem (a b : ℕ) (ha : a = 2 ∨ a = 3 ∨ a = 4) (hb : b = 2 ∨ b = 3 ∨ b = 4) (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ a) (RHSingDef0516.σ b)) (OOb a b i k) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp only [OOb, gzz]
  · exact OO22_mem i k hi hk
  · exact OO23_mem i k hi hk
  · exact OO24_mem i k hi hk
  · rw [OO_symm]; exact OO23_mem k i hk hi
  · exact OO33_mem i k hi hk
  · exact OO34_mem i k hi hk
  · rw [OO_symm]; exact OO24_mem k i hk hi
  · rw [OO_symm]; exact OO34_mem k i hk hi
  · exact OO44_mem i k hi hk


theorem gamB_mem (i k : ℕ) (hi : i < 64) (hk : k < 64)
    (hN : ∀ j < 64, 127 - j ≤ (RHNTab0515.tab.getD j []).length)
    (hK : ∀ j < 64, 127 - j ≤ (RHKTab0515.tab.getD j []).length) :
    mem S ((1 / 2) * (Mw (fun x => Real.log (1 + x) ^ 2) i k + Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k) +
      ((w 2 * (RHPairInt0516.F i k (RHSingDef0516.σ 2) + RHPairInt0516.F k i (RHSingDef0516.σ 2)) +
        (w 3 * (RHPairInt0516.F i k (RHSingDef0516.σ 3) + RHPairInt0516.F k i (RHSingDef0516.σ 3)) +
         w 4 * (RHPairInt0516.F i k (RHSingDef0516.σ 4) + RHPairInt0516.F k i (RHSingDef0516.σ 4)))) +
       ((((w 2 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)) * 2 +
          ((w 2 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 3)) * 2 +
           (w 2 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 4)) * 2)) +
         ((w 3 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 2)) * 2 +
          ((w 3 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 3)) * 2 +
           (w 3 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 4)) * 2)) +
         ((w 4 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 2)) * 2 +
          ((w 4 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 3)) * 2 +
           (w 4 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 4)) * 2))) +
        w 2 * w 2 * (RHPairInt0516.X i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2) +
          RHPairInt0516.X k i (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)))))
      (gamB i k) := by
  have hw : ∀ a, (a = 2 ∨ a = 3 ∨ a = 4) → mem S (w a) (wBm a) := fun a ha => wBm_mem a ha
  have hF : ∀ a, (a = 2 ∨ a = 3 ∨ a = 4) → mem S (w a * (RHPairInt0516.F i k (RHSingDef0516.σ a) +
      RHPairInt0516.F k i (RHSingDef0516.σ a))) (fterm a i k) := fun a ha =>
    mem_mulB hS (hw a ha) (mem_add (Fm_mem a ha i k hi hk) (Fm_mem a ha k i hk hi))
  have hO : ∀ a b, (a = 2 ∨ a = 3 ∨ a = 4) → (b = 2 ∨ b = 3 ∨ b = 4) →
      mem S ((w a * w b * RHPairInt0516.OO i k (RHSingDef0516.σ a) (RHSingDef0516.σ b)) * 2) (oterm a b i k) := by
    intro a b ha hb
    have := mem_smul hS 2 (d := 1) (by norm_num) (mem_mulB hS (mem_mulB hS (hw a ha) (hw b hb)) (OOb_mem a b ha hb i k hi hk))
    unfold oterm; simpa using this
  have hX : mem S (w 2 * w 2 * (RHPairInt0516.X i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2) +
      RHPairInt0516.X k i (RHSingDef0516.σ 2) (RHSingDef0516.σ 2))) (xterm i k) :=
    mem_mulB hS (mem_mulB hS (hw 2 (by decide)) (hw 2 (by decide)))
      (mem_add (XX_mem i k hi hk) (XX_mem k i hk hi))
  have hNK : mem S ((1 / 2) * (Mw (fun x => Real.log (1 + x) ^ 2) i k + Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k))
      (smul 1 2 (add (gzz RHNTab0515.tab i k) (gzz RHKTab0515.tab i k))) := by
    have := mem_smul hS 1 (d := 2) (by norm_num)
      (mem_add (tab_entry RHNTab0515.N_mem hN hi hk) (tab_entry RHKTab0515.K_mem hK hi hk))
    convert this using 1; push_cast; ring
  have A2 := RHBall0504.mem_add (hO 2 2 (by decide) (by decide))
    (RHBall0504.mem_add (hO 2 3 (by decide) (by decide)) (hO 2 4 (by decide) (by decide)))
  have A3 := RHBall0504.mem_add (hO 3 2 (by decide) (by decide))
    (RHBall0504.mem_add (hO 3 3 (by decide) (by decide)) (hO 3 4 (by decide) (by decide)))
  have A4 := RHBall0504.mem_add (hO 4 2 (by decide) (by decide))
    (RHBall0504.mem_add (hO 4 3 (by decide) (by decide)) (hO 4 4 (by decide) (by decide)))
  have hFs := RHBall0504.mem_add (hF 2 (by decide)) (RHBall0504.mem_add (hF 3 (by decide)) (hF 4 (by decide)))
  have hfin := RHBall0504.mem_add hNK (RHBall0504.mem_add hFs
    (RHBall0504.mem_add (RHBall0504.mem_add A2 (RHBall0504.mem_add A3 A4)) hX))
  unfold gamB
  convert hfin using 1
  ring

/-- The real value above equals `γ_ik = ∫ φ_i φ_k` for same-parity `i, k`. -/
theorem gam_value (i k : ℕ) (hpar : (i + k) % 2 = 0) :
    ∫ u in (-1:ℝ)..1, RHSingDef0516.phi i u * RHSingDef0516.phi k u =
    (1 / 2) * (Mw (fun x => Real.log (1 + x) ^ 2) i k + Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k) +
      ((w 2 * (RHPairInt0516.F i k (RHSingDef0516.σ 2) + RHPairInt0516.F k i (RHSingDef0516.σ 2)) +
        (w 3 * (RHPairInt0516.F i k (RHSingDef0516.σ 3) + RHPairInt0516.F k i (RHSingDef0516.σ 3)) +
         w 4 * (RHPairInt0516.F i k (RHSingDef0516.σ 4) + RHPairInt0516.F k i (RHSingDef0516.σ 4)))) +
       ((((w 2 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)) * 2 +
          ((w 2 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 3)) * 2 +
           (w 2 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 4)) * 2)) +
         ((w 3 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 2)) * 2 +
          ((w 3 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 3)) * 2 +
           (w 3 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 4)) * 2)) +
         ((w 4 * w 2 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 2)) * 2 +
          ((w 4 * w 3 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 3)) * 2 +
           (w 4 * w 4 * RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 4)) * 2))) +
        w 2 * w 2 * (RHPairInt0516.X i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2) +
          RHPairInt0516.X k i (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)))) := by
  have he : ((-1 : ℝ) ^ (i + k)) = 1 := Even.neg_one_pow (Nat.even_iff.mpr hpar)
  rw [RHGammaThm0516.gamma_eq, he]
  simp only [Fin.sum_univ_three, RHGammaExp0516.W, RHGammaExp0516.Sh, w, Fin.isValue]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

end RHGamSound0523

