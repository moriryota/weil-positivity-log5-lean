import JBounds0495
import Entry00_0495
import H0Bounds0472
import Constants0467
import Log2_100
import Log5Bound0473
import StepA1_G1

/-! # 0495 T4 pilot, final: rigorous enclosure of the even (0,0) low-block entry

`A0true false 0 0 ∈ [Alo, Ahi]`, width 2e-24, from: the closed form (step 1), the exact series
`J = 16 (S1 − r T)` (steps 2, 3c), the Euler–Maclaurin enclosure of `S1` (step 3a/b), and the
certified constants h0 (0472), log 2 (0455), log 3/√2/√3 (0467), log 5 (0473). -/

open scoped BigOperators
set_option maxHeartbeats 4000000

namespace RHEntry00Bounds0495
open RHLog5Bridge RHLowBlock0494 RHEntry00_0495 RHJBounds0495

def l2L : ℚ := 69314718055994530941723212145817 / 100000000000000000000000000000000
def l2H : ℚ := 34657359027997265470861606072909 / 50000000000000000000000000000000
def l3L : ℚ := 27465307216702742284881130923063 / 25000000000000000000000000000000
def l3H : ℚ := 109861228866810969139524523692253 / 100000000000000000000000000000000
def q2L : ℚ := 141421356237309504880168872420969 / 100000000000000000000000000000000
def q2H : ℚ := 14142135623730950488016887242097 / 10000000000000000000000000000000
def q3L : ℚ := 173205080756887729352744634150587 / 100000000000000000000000000000000
def q3H : ℚ := 43301270189221932338186158537647 / 25000000000000000000000000000000
def l5L : ℚ := 80471895621705018730037966661309 / 50000000000000000000000000000000
def l5H : ℚ := 160943791243410037460075933322619 / 100000000000000000000000000000000
def hL : ℚ := -21488733676902662328931829989799 / 4000000000000000000000000000000
def hH : ℚ := -268609170961283279111647874872487 / 50000000000000000000000000000000
def Alo : ℚ := 41730848611121622475041 / 500000000000000000000000
def Ahi : ℚ := 20865424305560811237521 / 250000000000000000000000

/-! ### working bounds (outward 32-digit roundings of the certified 100-digit enclosures) -/

lemma cast2 {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

lemma b_l2 : (l2L : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (l2H : ℝ) :=
  ⟨(cast2 (by decide +kernel : l2L ≤ Trial0455.lo)).trans Trial0455.log2_bounds.1,
   Trial0455.log2_bounds.2.trans (cast2 (by decide +kernel : Trial0455.hi ≤ l2H))⟩
lemma b_l3 : (l3L : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (l3H : ℝ) :=
  ⟨(cast2 (by decide +kernel : l3L ≤ RHConstants0467.log3Lo)).trans RHConstants0467.log3_bounds.1,
   RHConstants0467.log3_bounds.2.trans (cast2 (by decide +kernel : RHConstants0467.log3Hi ≤ l3H))⟩
lemma b_q2 : (q2L : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (q2H : ℝ) :=
  ⟨(cast2 (by decide +kernel : q2L ≤ RHConstants0467.sqrt2Lo)).trans RHConstants0467.sqrt2_bounds.1,
   RHConstants0467.sqrt2_bounds.2.trans (cast2 (by decide +kernel : RHConstants0467.sqrt2Hi ≤ q2H))⟩
lemma b_q3 : (q3L : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (q3H : ℝ) :=
  ⟨(cast2 (by decide +kernel : q3L ≤ RHConstants0467.sqrt3Lo)).trans RHConstants0467.sqrt3_bounds.1,
   RHConstants0467.sqrt3_bounds.2.trans (cast2 (by decide +kernel : RHConstants0467.sqrt3Hi ≤ q3H))⟩
lemma b_l5 : (l5L : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (l5H : ℝ) :=
  ⟨(cast2 (by decide +kernel : l5L ≤ Trial0456.lo)).trans Trial0456.log5_bounds.1,
   Trial0456.log5_bounds.2.trans (cast2 (by decide +kernel : Trial0456.hi ≤ l5H))⟩
lemma b_h : (hL : ℝ) ≤ h0c ∧ h0c ≤ (hH : ℝ) :=
  ⟨(cast2 (by decide +kernel : hL ≤ RHH0Numeric0472.h0Lo)).trans RHH0Numeric0472.h0_bounds.1,
   RHH0Numeric0472.h0_bounds.2.trans (cast2 (by decide +kernel : RHH0Numeric0472.h0Hi ≤ hH))⟩

/-! ### interval helpers (positive operands) -/

lemma mulI {a b al ah bl bh : ℝ} (ha : al ≤ a ∧ a ≤ ah) (hb : bl ≤ b ∧ b ≤ bh)
    (h1 : 0 ≤ al) (h2 : 0 ≤ bl) : al * bl ≤ a * b ∧ a * b ≤ ah * bh :=
  ⟨mul_le_mul ha.1 hb.1 h2 (h1.trans ha.1),
   mul_le_mul ha.2 hb.2 (h2.trans hb.1) (h1.trans (ha.1.trans ha.2))⟩

lemma divI {a b al ah bl bh : ℝ} (ha : al ≤ a ∧ a ≤ ah) (hb : bl ≤ b ∧ b ≤ bh)
    (h1 : 0 ≤ al) (h2 : 0 < bl) : al / bh ≤ a / b ∧ a / b ≤ ah / bl := by
  have hb0 : 0 < b := h2.trans_le hb.1
  have hbh : 0 < bh := hb0.trans_le hb.2
  constructor
  · calc al / bh ≤ a / bh := div_le_div_of_nonneg_right ha.1 hbh.le
      _ ≤ a / b := div_le_div_of_nonneg_left (h1.trans ha.1) hb0 hb.2
  · calc a / b ≤ ah / b := div_le_div_of_nonneg_right ha.2 hb0.le
      _ ≤ ah / bl := div_le_div_of_nonneg_left (h1.trans (ha.1.trans ha.2)) h2 hb.1

/-! ### exact identity -/

noncomputable def Pn : ℝ :=
  Real.log 2 / Real.sqrt 2 * (Real.log 5 - Real.log 2) +
  Real.log 3 / Real.sqrt 3 * (Real.log 5 - Real.log 3) +
  Real.log 2 / 2 * (Real.log 5 - 2 * Real.log 2)

noncomputable def X : ℝ :=
  4 * (RHHurwitzEM0495.S1 - r * T) + 4 * (1 / r + r - 2) - Pn

lemma sinh_sq : Real.sinh (halfWidth / 2) ^ 2 = (1 / r + r - 2) / 4 := by
  have h1 : Real.exp (halfWidth / 2) ^ 2 = Real.exp halfWidth := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp (-(halfWidth / 2)) ^ 2 = Real.exp (-halfWidth) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (halfWidth / 2) * Real.exp (-(halfWidth / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hir : 1 / r = Real.exp halfWidth := by unfold r; rw [Real.exp_neg, one_div, inv_inv]
  rw [Real.sinh_eq, hir]
  unfold r
  linear_combination (1/4 : ℝ) * h1 - (1/2 : ℝ) * h3 + (1/4 : ℝ) * h2

lemma prime_sum : (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (2 * halfWidth - Real.log n)) = Pn := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  rw [RHStepA1G1.vm_zero, RHStepA1G1.vm_one, RHStepA1G1.vm_two, RHStepA1G1.vm_three, RHStepA1G1.vm_four,
    two_L, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
    Real.log_pow]
  unfold Pn
  push_cast
  ring

theorem A00_eq : A0true false 0 0 = h0c + 2 * X / Real.log 5 := by
  rw [entry00_closed, J_eq, sinh_sq, prime_sum]
  have hL : Real.log 5 ≠ 0 := by positivity
  rw [← two_L]
  have hw : halfWidth ≠ 0 := halfWidth_pos.ne'
  unfold X
  field_simp
  ring

/-! ### interval propagation -/

def Xlo : ℚ := 4 * (RHS1Numeric0495.S1Lo - rHi * (TM + Ttail)) + 4 * (1 / rHi + rLo - 2) -
    ((l2H / q2L) * (l5H - l2L) + (l3H / q3L) * (l5H - l3L) + (l2H / 2) * (l5H - 2 * l2L))
def Xhi : ℚ := 4 * (RHS1Numeric0495.S1Hi - rLo * TM) + 4 * (1 / rLo + rHi - 2) -
    ((l2L / q2H) * (l5L - l2H) + (l3L / q3H) * (l5L - l3H) + (l2L / 2) * (l5L - 2 * l2H))

lemma nn {a : ℚ} (h : 0 ≤ a) : (0:ℝ) ≤ (a : ℝ) := by exact_mod_cast h
lemma ps {a : ℚ} (h : 0 < a) : (0:ℝ) < (a : ℝ) := by exact_mod_cast h

theorem X_bounds : (Xlo : ℝ) ≤ X ∧ X ≤ (Xhi : ℝ) := by
  obtain ⟨hr1, hr2⟩ := r_bounds
  obtain ⟨hT1, hT2⟩ := T_bounds
  obtain ⟨hS1, hS2⟩ := RHS1Numeric0495.S1_bounds
  have hrT := mulI ⟨hr1, hr2⟩ ⟨hT1, hT2⟩ (nn (by decide +kernel)) (nn (by decide +kernel))
  have hinv := divI (a := 1) (al := 1) (ah := 1) ⟨le_rfl, le_rfl⟩ ⟨hr1, hr2⟩ zero_le_one
    (ps (by decide +kernel))
  have hP1 := mulI (divI b_l2 b_q2 (nn (by decide +kernel)) (ps (by decide +kernel)))
    (⟨by linarith [b_l5.1, b_l2.2], by linarith [b_l5.2, b_l2.1]⟩ :
      ((l5L : ℝ) - l2H) ≤ Real.log 5 - Real.log 2 ∧ Real.log 5 - Real.log 2 ≤ (l5H : ℝ) - l2L)
    (div_nonneg (nn (by decide +kernel)) (nn (by decide +kernel)))
    (by have h := nn (a := l5L - l2H) (by decide +kernel); push_cast at h; exact h)
  have hP2 := mulI (divI b_l3 b_q3 (nn (by decide +kernel)) (ps (by decide +kernel)))
    (⟨by linarith [b_l5.1, b_l3.2], by linarith [b_l5.2, b_l3.1]⟩ :
      ((l5L : ℝ) - l3H) ≤ Real.log 5 - Real.log 3 ∧ Real.log 5 - Real.log 3 ≤ (l5H : ℝ) - l3L)
    (div_nonneg (nn (by decide +kernel)) (nn (by decide +kernel)))
    (by have h := nn (a := l5L - l3H) (by decide +kernel); push_cast at h; exact h)
  have hP3 := mulI
    (⟨by linarith [b_l2.1], by linarith [b_l2.2]⟩ :
      (l2L : ℝ) / 2 ≤ Real.log 2 / 2 ∧ Real.log 2 / 2 ≤ (l2H : ℝ) / 2)
    (⟨by linarith [b_l5.1, b_l2.2], by linarith [b_l5.2, b_l2.1]⟩ :
      ((l5L : ℝ) - 2 * l2H) ≤ Real.log 5 - 2 * Real.log 2 ∧ Real.log 5 - 2 * Real.log 2 ≤ (l5H : ℝ) - 2 * l2L)
    (by have h := nn (a := l2L / 2) (by decide +kernel); push_cast at h; exact h)
    (by have h := nn (a := l5L - 2 * l2H) (by decide +kernel); push_cast at h; exact h)
  unfold X Pn
  simp only [Xlo, Xhi]
  push_cast
  constructor <;> linarith [hrT.1, hrT.2, hinv.1, hinv.2, hP1.1, hP1.2, hP2.1, hP2.2, hP3.1, hP3.2]

theorem A00_bounds : (Alo : ℝ) ≤ A0true false 0 0 ∧ A0true false 0 0 ≤ (Ahi : ℝ) := by
  have hX := X_bounds
  have hX2 : ((2 * Xlo : ℚ) : ℝ) ≤ 2 * X ∧ 2 * X ≤ ((2 * Xhi : ℚ) : ℝ) := by
    push_cast; exact ⟨by linarith [hX.1], by linarith [hX.2]⟩
  have hD := divI hX2 b_l5 (nn (by decide +kernel)) (ps (by decide +kernel))
  rw [A00_eq]
  have e1 : (Alo : ℝ) ≤ (hL : ℝ) + ((2 * Xlo : ℚ) : ℝ) / l5H := by
    have h := cast2 (by decide +kernel : Alo ≤ hL + 2 * Xlo / l5H); push_cast at h ⊢; exact h
  have e2 : (hH : ℝ) + ((2 * Xhi : ℚ) : ℝ) / l5L ≤ (Ahi : ℝ) := by
    have h := cast2 (by decide +kernel : hH + 2 * Xhi / l5L ≤ Ahi); push_cast at h ⊢; exact h
  constructor <;> linarith [b_h.1, b_h.2, hD.1, hD.2]

theorem A00_width : Ahi - Alo ≤ (1 : ℚ) / 10 ^ 23 := by decide +kernel

end RHEntry00Bounds0495

