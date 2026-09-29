import FSound0523
import OO22_0522
import OO23_0522
import OO24_0522
import OO33_0522
import OO34_0522
import OO44_0522
import XX_0522

/-! # 0523: soundness of the overlap stages: `OO i k σ_a σ_b` (a ≤ b) and `X i k σ_2 σ_2`. -/

open Finset
open scoped BigOperators

namespace RHOOSound0523
open RHBall0504 RHBallVec0504 RHBallDot0509 RHG6Core0522 RHPrBall0511 RHPrAff0511 RHFamDefs0522 RHFSound0523

local notation "S" => (2:ℕ) ^ 256

theorem dot_gen {α γ₁ γ₂ : ℝ} {aB g1 g2 : Ball} (ha : mem S α aB) (h1 : mem S γ₁ g1) (h2 : mem S γ₂ g2)
    (L R T : List (List Ball)) (hL : L = afAll S aB g1 64) (hR : R = afAll S aB g2 64)
    (hT : T = L.map (fun Li => R.map (fun Rk => mulB S aB (dB S Li Rk))))
    (hlL : L.length = 64) (hlR : R.length = 64) (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (α * ∑ j ∈ range (i + 1), Af α γ₁ i j * Af α γ₂ k j * (2 / (2 * j + 1))) (gz (T.getD i []) k) := by
  have hA : VecMem S (Af α γ₁ i) (L.getD i []) := by rw [hL]; exact afAll_mem RHFSound0523.hS ha h1 64 i hi
  have hB : VecMem S (Af α γ₂ k) (R.getD k []) := by rw [hR]; exact afAll_mem RHFSound0523.hS ha h2 64 k hk
  have hd := dB_mem RHFSound0523.hS hA hB (i + 1) (fun j hj => Af_supp _ _ i j hj)
  have e : gz (T.getD i []) k = mulB S aB (dB S (L.getD i []) (R.getD k [])) := by
    rw [hT, getD_map (by rw [hlL]; exact hi)]
    unfold gz
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < R.length by rw [hlR]; exact hk)]
  rw [e]; exact mem_mulB RHFSound0523.hS ha hd

lemma sig_pos {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) : 0 < RHSingDef0516.σ m := by
  rcases hm with rfl | rfl | rfl <;>
  · unfold RHSingDef0516.σ; exact div_pos (Real.log_pos (by norm_num)) RHLog5Bridge.halfWidth_pos

lemma sig_lt2 {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) : RHSingDef0516.σ m < 2 := by
  unfold RHSingDef0516.σ
  rw [div_lt_iff₀ RHLog5Bridge.halfWidth_pos, RHLog5Bridge.twice_halfWidth]
  rcases hm with rfl | rfl | rfl <;> exact Real.log_lt_log (by norm_num) (by norm_num)

lemma sig_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : RHSingDef0516.σ a ≤ RHSingDef0516.σ b := by
  unfold RHSingDef0516.σ
  apply div_le_div_of_nonneg_right _ RHLog5Bridge.halfWidth_pos.le
  exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)

theorem OO22_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)) (gz (RHOO22_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 2) (RHSingDef0516.σ 2) = RHSingDef0516.σ 2 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 2) (by decide)) (g1B_mem (m := 2) (by decide)) (g1B_mem (m := 2) (by decide))
    RHFamB_0522.famB2 RHFamB_0522.famB2 RHOO22_0522.tab RHFamB_0522.famB2_eq RHFamB_0522.famB2_eq RHOO22_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem OO23_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 3)) (gz (RHOO23_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 2) (RHSingDef0516.σ 3) = RHSingDef0516.σ 3 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 3) (by decide)) (crossB_mem (a := 2) (b := 3) (by decide) (by decide)) (g1B_mem (m := 3) (by decide))
    RHFamX_0522.cr23 RHFamB_0522.famB3 RHOO23_0522.tab RHFamX_0522.cr23_eq RHFamB_0522.famB3_eq RHOO23_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem OO24_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 4)) (gz (RHOO24_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 2) (RHSingDef0516.σ 4) = RHSingDef0516.σ 4 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 4) (by decide)) (crossB_mem (a := 2) (b := 4) (by decide) (by decide)) (g1B_mem (m := 4) (by decide))
    RHFamX_0522.cr24 RHFamB_0522.famB4 RHOO24_0522.tab RHFamX_0522.cr24_eq RHFamB_0522.famB4_eq RHOO24_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem OO33_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 3)) (gz (RHOO33_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 3) (RHSingDef0516.σ 3) = RHSingDef0516.σ 3 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 3) (by decide)) (g1B_mem (m := 3) (by decide)) (g1B_mem (m := 3) (by decide))
    RHFamB_0522.famB3 RHFamB_0522.famB3 RHOO33_0522.tab RHFamB_0522.famB3_eq RHFamB_0522.famB3_eq RHOO33_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem OO34_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 3) (RHSingDef0516.σ 4)) (gz (RHOO34_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 3) (RHSingDef0516.σ 4) = RHSingDef0516.σ 4 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 4) (by decide)) (crossB_mem (a := 3) (b := 4) (by decide) (by decide)) (g1B_mem (m := 4) (by decide))
    RHFamX_0522.cr34 RHFamB_0522.famB4 RHOO34_0522.tab RHFamX_0522.cr34_eq RHFamB_0522.famB4_eq RHOO34_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem OO44_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.OO i k (RHSingDef0516.σ 4) (RHSingDef0516.σ 4)) (gz (RHOO44_0522.tab.getD i []) k) := by
  have hmax : max (RHSingDef0516.σ 4) (RHSingDef0516.σ 4) = RHSingDef0516.σ 4 :=
    max_eq_right (sig_mono (by norm_num) (by norm_num))
  rw [RHAffRed0516.OO_eq i k (sig_lt2 (by decide)) (sig_lt2 (by decide)), hmax]
  have h := dot_gen (alphaB_mem (m := 4) (by decide)) (g1B_mem (m := 4) (by decide)) (g1B_mem (m := 4) (by decide))
    RHFamB_0522.famB4 RHFamB_0522.famB4 RHOO44_0522.tab RHFamB_0522.famB4_eq RHFamB_0522.famB4_eq RHOO44_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

theorem XX_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.X i k (RHSingDef0516.σ 2) (RHSingDef0516.σ 2)) (gz (RHXX_0522.tab.getD i []) k) := by
  have hst : RHSingDef0516.σ 2 + RHSingDef0516.σ 2 < 2 := by
    rw [RHGammaFull0516.sig_add 2 2 (by norm_num) (by norm_num), div_lt_iff₀ RHGammaFull0516.log5_pos]
    have : Real.log ((2:ℕ) * (2:ℕ) : ℝ) < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  rw [RHAffRed0516.X_eq i k hst]
  have h := dot_gen oneMsB_mem nsigB_mem (sigB_mem 2 (Or.inl rfl))
    RHFamX_0522.famXm RHFamX_0522.famXp RHXX_0522.tab RHFamX_0522.famXm_eq RHFamX_0522.famXp_eq RHXX_0522.tab_eq
    (by decide +kernel) (by decide +kernel) i k hi hk
  convert h using 2
  · ring
  · refine sum_congr rfl (fun j _ => ?_)
    congr 2 <;> [congr 1; congr 1] <;> ring

end RHOOSound0523

