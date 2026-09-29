import Const0521
import PrBall0511

/-! # 0522: ball constants for the affine families (from `Const0521`) and their enclosures. -/

namespace RHFamDefs0522
open RHBall0504 RHConst0521

def sigB : ℕ → Ball
  | 2 => sig2 | 3 => sig3 | _ => sig4

def alphaB (m : ℕ) : Ball := sub ((2 ^ 256 : ℕ), 0) (smul 1 2 (sigB m))
def g2B (m : ℕ) : Ball := smul 1 2 (sigB m)
def g1B (m : ℕ) : Ball := neg (smul 1 2 (sigB m))
def crossB (a b : ℕ) : Ball := sub (smul 1 2 (sigB b)) (sigB a)
def oneMsB : Ball := sub ((2 ^ 256 : ℕ), 0) (sigB 2)
def nsigB : Ball := neg (sigB 2)

lemma hS : 0 < (2:ℕ) ^ 256 := by positivity

lemma sigB_mem (m : ℕ) (hm : m = 2 ∨ m = 3 ∨ m = 4) : mem (2 ^ 256) (RHSingDef0516.σ m) (sigB m) := by
  rcases hm with rfl | rfl | rfl
  · exact sig2_mem
  · exact sig3_mem
  · exact sig4_mem

lemma one_mem : mem (2 ^ 256) 1 (((2 ^ 256 : ℕ) : ℤ), 0) := by
  unfold mem; simp

lemma half_mem {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) :
    mem (2 ^ 256) (RHSingDef0516.σ m / 2) (smul 1 2 (sigB m)) := by
  have h := mem_smul hS 1 (d := 2) (by norm_num) (sigB_mem m hm)
  simpa using h

theorem alphaB_mem {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) :
    mem (2 ^ 256) (1 - RHSingDef0516.σ m / 2) (alphaB m) := mem_sub one_mem (half_mem hm)
theorem g2B_mem {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) :
    mem (2 ^ 256) (RHSingDef0516.σ m / 2) (g2B m) := half_mem hm
theorem g1B_mem {m : ℕ} (hm : m = 2 ∨ m = 3 ∨ m = 4) :
    mem (2 ^ 256) (-(RHSingDef0516.σ m / 2)) (g1B m) := mem_neg (half_mem hm)
theorem crossB_mem {a b : ℕ} (ha : a = 2 ∨ a = 3 ∨ a = 4) (hb : b = 2 ∨ b = 3 ∨ b = 4) :
    mem (2 ^ 256) (RHSingDef0516.σ b / 2 - RHSingDef0516.σ a) (crossB a b) := mem_sub (half_mem hb) (sigB_mem a ha)
theorem oneMsB_mem : mem (2 ^ 256) (1 - RHSingDef0516.σ 2) oneMsB := mem_sub one_mem (sigB_mem 2 (Or.inl rfl))
theorem nsigB_mem : mem (2 ^ 256) (-(RHSingDef0516.σ 2)) nsigB := mem_neg (sigB_mem 2 (Or.inl rfl))

end RHFamDefs0522

