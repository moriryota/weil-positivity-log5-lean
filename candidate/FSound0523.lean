import MkSound0523
import G6Core0522
import FRed0516
import MpTab0515
import FFm2_0522
import FF3_0522
import FFm4_0522

/-! # 0523: soundness of the F stage: `gz (Fm.getD i []) k ∋ F i k σ_m` for `i, k < 64`. -/

open Finset
open scoped BigOperators

namespace RHFSound0523
open RHBall0504 RHBallVec0504 RHBallDot0509 RHRec2D0515 RHG6Core0522 RHPrBall0511 RHPrAff0511 RHFamDefs0522

local notation "S" => (2:ℕ) ^ 256

lemma hS : 0 < S := by positivity

def signed (j : ℕ) (row : List Ball) : List Ball := mapI (fun jj b => if (j + jj) % 2 = 0 then b else neg b) 0 row

lemma neg_one_pow_of_mod {n : ℕ} : (-1 : ℝ) ^ n = if n % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.mp h]; omega)]

lemma signed_mem {P : ℕ → ℝ} {row : List Ball} (h : VecMem S P row) (j : ℕ) :
    VecMem S (fun jj => (-1) ^ (j + jj) * P jj) (signed j row) := by
  refine vecMem_mapI hS _ h (fun l hl => ?_) (fun l hl => by simp [hl])
  rw [neg_one_pow_of_mod]
  split_ifs with he
  · simpa using hl
  · simpa using mem_neg hl

lemma row_mem {P K : ℕ → ℝ} {rP rK : List Ball} (hP : RowMem S P rP) (hK : RowMem S K rK)
    (hlP : 64 ≤ rP.length) (hlK : 64 ≤ rK.length) (j : ℕ) :
    VecMem S (RHG6Core0522.trunc 64 (fun jj => (-1) ^ (j + jj) * P jj + K jj)) (vadd (signed j (rP.take 64)) (rK.take 64)) := by
  have h1 := signed_mem (vecMem_take hS hP hlP) j
  have h2 := vecMem_take hS hK hlK
  have h := vecMem_vadd h1 h2
  convert h using 1
  funext jj; unfold RHG6Core0522.trunc; split_ifs <;> simp

lemma getD_map_range {f : ℕ → List Ball} {j N : ℕ} (hj : j < N) : ((List.range N).map f).getD j [] = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

lemma getD_map {L : List (List Ball)} {f : List Ball → List Ball} {j : ℕ} (hj : j < L.length) :
    (L.map f).getD j [] = f (L.getD j []) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gz_zip_map {L1 L2 : List (List Ball)} {f : List Ball × List Ball → Ball} {k : ℕ}
    (h1 : k < L1.length) (h2 : k < L2.length) :
    gz ((List.zip L1 L2).map f) k = f (L1.getD k [], L2.getD k []) := by
  unfold gz
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, h1, h2]

theorem F_ball {A B : ℕ → ℝ} {M : ℕ → ℕ → ℝ} {Al Bl Yl : List Ball} {α ℓ : ℝ} {αB ℓB : Ball}
    (hA : VecMem S A Al) (hB : VecMem S B Bl)
    (hY : VecMem S (fun j => if j < 64 then ∑ j' ∈ range 64, M j j' * B j' else 0) Yl)
    (hα : mem S α αB) (hℓ : mem S ℓ ℓB) (hA0 : ∀ j, 64 ≤ j → A j = 0) :
    mem S (α * (ℓ * ∑ j ∈ range 64, A j * B j * (2 / (2 * j + 1)) +
        ∑ j ∈ range 64, ∑ j' ∈ range 64, A j * B j' * M j j'))
      (mulB S αB (add (mulB S ℓB (dB S Al Bl)) (dotB S Al Yl))) := by
  have h1 := dB_mem hS hA hB 64 hA0
  have h2 := dot_mem hS hA hY 64 hA0 (fun j hj => by simp [show ¬ j < 64 by omega])
  have e : ∑ j ∈ range 64, A j * (if j < 64 then ∑ j' ∈ range 64, M j j' * B j' else 0) =
      ∑ j ∈ range 64, ∑ j' ∈ range 64, A j * B j' * M j j' := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [if_pos (mem_range.mp hj), mul_sum]
    exact sum_congr rfl (fun j' _ => by ring)
  rw [e] at h2
  exact mem_mulB hS hα (mem_add (mem_mulB hS hℓ h1) h2)

lemma sum_supp64 {N : ℕ} (hN : N ≤ 64) {g : ℕ → ℝ} (hg : ∀ j, N ≤ j → g j = 0) :
    ∑ j ∈ range 64, g j = ∑ j ∈ range N, g j := sum_range_of_supp hN hg

theorem F_mem_gen {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4)
    (famA famB Mm Y Fm Pt Kt : List (List Ball)) (ℓB : Ball)
    (hfA : famA = afAll S (alphaB m) (g2B m) 64) (hfB : famB = afAll S (alphaB m) (g1B m) 64)
    (hMm : Mm = (List.range 64).map (fun j => vadd (signed j ((Pt.getD j []).take 64)) ((Kt.getD j []).take 64)))
    (hY : Y = famB.map (fun Bk => dotRows S Mm Bk))
    (hF : ∀ i < 64, Fm.getD i [] = (List.zip famB Y).map (fun p =>
      mulB S (alphaB m) (add (mulB S ℓB (dB S (famA.getD i []) p.1)) (dotB S (famA.getD i []) p.2))))
    (hlA : famA.length = 64) (hlB : famB.length = 64)
    (hP : ∀ j, RowMem S (Mw (fun t => Real.log (1 + t)) j) (Pt.getD j []))
    (hK : ∀ j, RowMem S (Mw (fun t => Real.log (1 + RHMkSound0523.kap m * t)) j) (Kt.getD j []))
    (hPl : ∀ j < 64, 64 ≤ (Pt.getD j []).length) (hKl : ∀ j < 64, 64 ≤ (Kt.getD j []).length)
    (hℓ : mem S (Real.log (1 - RHSingDef0516.σ m / 2) + Real.log (1 + RHSingDef0516.σ m / 2)) ℓB)
    (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.F i k (RHSingDef0516.σ m)) (gz (Fm.getD i []) k) := by
  have hs0 : 0 < RHSingDef0516.σ m := by
    rcases hm with rfl | rfl | rfl <;>
    · unfold RHSingDef0516.σ; exact div_pos (Real.log_pos (by norm_num)) RHLog5Bridge.halfWidth_pos
  have hs2 : RHSingDef0516.σ m < 2 := by
    unfold RHSingDef0516.σ
    rw [div_lt_iff₀ RHLog5Bridge.halfWidth_pos, RHLog5Bridge.twice_halfWidth]
    rcases hm with rfl | rfl | rfl <;> exact Real.log_lt_log (by norm_num) (by norm_num)
  -- vectors
  have hA : VecMem S (Af (1 - RHSingDef0516.σ m / 2) (RHSingDef0516.σ m / 2) i) (famA.getD i []) := by
    rw [hfA]; exact afAll_mem hS (alphaB_mem hm) (g2B_mem hm) 64 i hi
  have hB : VecMem S (Af (1 - RHSingDef0516.σ m / 2) (-(RHSingDef0516.σ m / 2)) k) (famB.getD k []) := by
    rw [hfB]; exact afAll_mem hS (alphaB_mem hm) (g1B_mem hm) 64 k hk
  set M : ℕ → ℕ → ℝ := fun j => RHG6Core0522.trunc 64 (fun jj => (-1) ^ (j + jj) * Mw (fun t => Real.log (1 + t)) j jj +
    Mw (fun t => Real.log (1 + RHMkSound0523.kap m * t)) j jj) with hMdef
  have hMrows : ∀ j < 64, VecMem S (M j) (Mm.getD j []) := by
    intro j hj
    rw [hMm, getD_map_range hj]
    exact row_mem (hP j) (hK j) (hPl j hj) (hKl j hj) j
  have hlM : Mm.length = 64 := by rw [hMm]; simp
  have hM0 : ∀ j < 64, ∀ j', 64 ≤ j' → M j j' = 0 := fun j _ j' hj' => by
    simp [hMdef, RHG6Core0522.trunc, show ¬ j' < 64 by omega]
  have hB0 : ∀ j, 64 ≤ j → Af (1 - RHSingDef0516.σ m / 2) (-(RHSingDef0516.σ m / 2)) k j = 0 :=
    fun j hj => Af_supp _ _ k j (by omega)
  have hA0 : ∀ j, 64 ≤ j → Af (1 - RHSingDef0516.σ m / 2) (RHSingDef0516.σ m / 2) i j = 0 :=
    fun j hj => Af_supp _ _ i j (by omega)
  have hYk : VecMem S (fun j => if j < 64 then ∑ j' ∈ range 64, M j j' *
      Af (1 - RHSingDef0516.σ m / 2) (-(RHSingDef0516.σ m / 2)) k j' else 0) (Y.getD k []) := by
    rw [hY, getD_map (by rw [hlB]; exact hk)]
    exact dotRows_mem hS 64 hlM hMrows hB hM0 hB0
  have hlY : Y.length = 64 := by rw [hY, List.length_map, hlB]
  have hFik : gz (Fm.getD i []) k = mulB S (alphaB m) (add (mulB S ℓB (dB S (famA.getD i []) (famB.getD k [])))
      (dotB S (famA.getD i []) (Y.getD k []))) := by
    rw [hF i hi, gz_zip_map (by rw [hlB]; exact hk) (by rw [hlY]; exact hk)]
  have hA0' : ∀ j, i + 1 ≤ j → Af (1 - RHSingDef0516.σ m / 2) (RHSingDef0516.σ m / 2) i j = 0 :=
    fun j hj => Af_supp _ _ i j hj
  have hB0' : ∀ j, k + 1 ≤ j → Af (1 - RHSingDef0516.σ m / 2) (-(RHSingDef0516.σ m / 2)) k j = 0 :=
    fun j hj => Af_supp _ _ k j hj
  rw [hFik]
  have hball := F_ball hA hB hYk (alphaB_mem hm) hℓ hA0
  convert hball using 1
  -- identify with F_eq
  rw [RHFRed0516.F_eq i k hs0 hs2, show RHSingDef0516.σ m / 2 - RHSingDef0516.σ m = -(RHSingDef0516.σ m / 2) by ring]
  congr 1
  congr 1
  · congr 1
    exact (sum_supp64 (by omega) (fun j hj => by rw [hA0' j hj]; ring)).symm
  · rw [sum_supp64 (N := i + 1) (by omega) (fun j hj => by
      rw [sum_eq_zero (fun j' _ => by rw [Af_supp _ _ i j (by omega)]; ring)])]
    refine sum_congr rfl (fun j hj => ?_)
    rw [sum_supp64 (N := k + 1) (by omega) (fun j' hj' => by rw [hB0' j' hj']; ring)]
    refine sum_congr rfl (fun j' hj' => ?_)
    have hj'64 : j' < 64 := by simp at hj'; omega
    simp only [hMdef, RHG6Core0522.trunc, if_pos hj'64, RHMkSound0523.kap]

lemma Pl : ∀ j < 64, 64 ≤ (RHMpTab0515.tab.getD j []).length := by
  have h : (List.range 64).all (fun j => decide (64 ≤ (RHMpTab0515.tab.getD j []).length)) = true := by decide +kernel
  intro j hj; simpa [List.all_eq_true, hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

lemma Kl2 : ∀ j < 64, 64 ≤ (RHMkTab2_0521.tab.getD j []).length := by
  have h : (List.range 64).all (fun j => decide (64 ≤ (RHMkTab2_0521.tab.getD j []).length)) = true := by decide +kernel
  intro j hj; simpa [List.all_eq_true, hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

theorem F2_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.F i k (RHSingDef0516.σ 2)) (gz (RHFFm2_0522.Fm.getD i []) k) :=
  F_mem_gen (m := 2) (by decide) RHFamA_0522.famA2 RHFamB_0522.famB2 RHFY2_0522.Mm RHFY2_0522.Y
    RHFFm2_0522.Fm RHMpTab0515.tab RHMkTab2_0521.tab RHConst0521.ell2
    RHFamA_0522.famA2_eq RHFamB_0522.famB2_eq RHFY2_0522.Mm_eq RHFY2_0522.Y_eq (fun i hi => RHFFm2_0522.Fm_row i hi)
    (by decide +kernel) (by decide +kernel) RHMpTab0515.Mp_mem RHMkSound0523.Mk2_mem Pl Kl2
    RHConst0521.ell2_mem i k hi hk

lemma Kl3 : ∀ j < 64, 64 ≤ (RHMkTab3_0521.tab.getD j []).length := by
  have h : (List.range 64).all (fun j => decide (64 ≤ (RHMkTab3_0521.tab.getD j []).length)) = true := by decide +kernel
  intro j hj; simpa [List.all_eq_true, hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

theorem F3_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.F i k (RHSingDef0516.σ 3)) (gz (RHFF3_0522.Fm.getD i []) k) :=
  F_mem_gen (m := 3) (by decide) RHFamA_0522.famA3 RHFamB_0522.famB3 RHFY3_0522.Mm RHFY3_0522.Y
    RHFF3_0522.Fm RHMpTab0515.tab RHMkTab3_0521.tab RHConst0521.ell3
    RHFamA_0522.famA3_eq RHFamB_0522.famB3_eq RHFY3_0522.Mm_eq RHFY3_0522.Y_eq
    (fun i hi => by
      have hl : RHFamA_0522.famA3.length = 64 := by decide +kernel
      rw [RHFF3_0522.Fm_eq, getD_map (by rw [hl]; exact hi)]; rfl)
    (by decide +kernel) (by decide +kernel) RHMpTab0515.Mp_mem RHMkSound0523.Mk3_mem Pl Kl3
    RHConst0521.ell3_mem i k hi hk

lemma Kl4 : ∀ j < 64, 64 ≤ (RHMkTab4_0521.tab.getD j []).length := by
  have h : (List.range 64).all (fun j => decide (64 ≤ (RHMkTab4_0521.tab.getD j []).length)) = true := by decide +kernel
  intro j hj; simpa [List.all_eq_true, hj] using (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

theorem F4_mem (i k : ℕ) (hi : i < 64) (hk : k < 64) :
    mem S (RHPairInt0516.F i k (RHSingDef0516.σ 4)) (gz (RHFFm4_0522.Fm.getD i []) k) :=
  F_mem_gen (m := 4) (by decide) RHFamA_0522.famA4 RHFamB_0522.famB4 RHFY4_0522.Mm RHFY4_0522.Y
    RHFFm4_0522.Fm RHMpTab0515.tab RHMkTab4_0521.tab RHConst0521.ell4
    RHFamA_0522.famA4_eq RHFamB_0522.famB4_eq RHFY4_0522.Mm_eq RHFY4_0522.Y_eq (fun i hi => RHFFm4_0522.Fm_row i hi)
    (by decide +kernel) (by decide +kernel) RHMpTab0515.Mp_mem RHMkSound0523.Mk4_mem Pl Kl4
    RHConst0521.ell4_mem i k hi hk

end RHFSound0523

