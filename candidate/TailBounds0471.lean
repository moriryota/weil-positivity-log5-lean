import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Analysis.SpecialFunctions.Artanh
import PiBounds0466
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # 0471: rational enclosure of the fixed log5 tail `2*(atanh x + arctan x)`, `x = exp(-log 5/4)`

* `x^4 = 1/5` (exp algebra), so `x` lies in the continued-fraction bracket `[xLo, xHi]`
  (checked by `5 p^4 ≤ q^4` style rational comparisons with `decide +kernel`).
* `Real.atanh` in this environment is LeanCert's `(1/2) * log ((1+x)/(1-x))`
  (`LeanCert/Core/Expr.lean`); `(1+x)/(1-x)` is enclosed by monotonicity and pushed
  through `IntervalRat.logComputable` (soundness `IntervalRat.mem_logComputable`).
* `arctan` is monotone; the rational endpoints use 0466 `RHPi0466.arctan_bounds`.
* `atanh_eq_artanh` / `tailExpr_eq_T_tail_form` relate the statement to Mathlib's
  `Real.artanh` and to the main-system shape `2*(artanh (exp (-b/2)) + arctan (exp (-b/2)))`,
  `b = log 5 / 2`. -/

open LeanCert.Core RHPi0466

namespace RHTailNumeric0471

noncomputable def tailExpr : ℝ :=
  2 * (Real.atanh (Real.exp (-Real.log 5 / 4)) + Real.arctan (Real.exp (-Real.log 5 / 4)))

def xLo : ℚ := 978659385107457078783630057929362632802177658232773/1463437118751145056289559676868480969327460429978139
def xHi : ℚ := 322929146584188615083093035309031347272003936715357/482891705765475320245082655482577761565902964746614

theorem x_pow_four : Real.exp (-Real.log 5 / 4) ^ 4 = 1 / 5 := by
  rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * (-Real.log 5 / 4) = -Real.log 5 by push_cast; ring,
    Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem xLo_check : 0 ≤ xLo ∧ xLo ^ 4 ≤ 1 / 5 := by decide +kernel
theorem xHi_check : 0 ≤ xHi ∧ 1 / 5 ≤ xHi ^ 4 ∧ xHi < 1 := by decide +kernel

theorem x_bounds :
    (xLo : ℝ) ≤ Real.exp (-Real.log 5 / 4) ∧ Real.exp (-Real.log 5 / 4) ≤ (xHi : ℝ) := by
  have hx := Real.exp_pos (-Real.log 5 / 4)
  have h4 := x_pow_four
  have hl0 : (0 : ℝ) ≤ xLo := by exact_mod_cast xLo_check.1
  have hh0 : (0 : ℝ) ≤ xHi := by exact_mod_cast xHi_check.1
  have hl : (xLo : ℝ) ^ 4 ≤ 1 / 5 := by
    have := (Rat.cast_le (K := ℝ)).mpr xLo_check.2
    push_cast at this
    exact this
  have hh : (1 / 5 : ℝ) ≤ (xHi : ℝ) ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).mpr xHi_check.2.1
    push_cast at this
    exact this
  constructor
  · by_contra h
    have := pow_lt_pow_left₀ (not_le.mp h) hx.le (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  · by_contra h
    have := pow_lt_pow_left₀ (not_le.mp h) hh0 (by norm_num : (4 : ℕ) ≠ 0)
    linarith

/-- Rational interval containing `(1+x)/(1-x)`. -/
def ratioInterval : IntervalRat := ⟨(1 + xLo) / (1 - xLo), (1 + xHi) / (1 - xHi), by decide +kernel⟩

def logEnclosure : IntervalRat := IntervalRat.logComputable ratioInterval 220

theorem ratio_mem :
    (1 + Real.exp (-Real.log 5 / 4)) / (1 - Real.exp (-Real.log 5 / 4)) ∈ ratioInterval := by
  obtain ⟨hl, hh⟩ := x_bounds
  have hh1 : (xHi : ℝ) < 1 := by exact_mod_cast xHi_check.2.2
  have hl0 : (0 : ℝ) ≤ xLo := by exact_mod_cast xLo_check.1
  rw [IntervalRat.mem_def]
  simp only [ratioInterval]
  push_cast
  constructor
  · exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  · exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

theorem atanh_bounds :
    ((logEnclosure.lo / 2 : ℚ) : ℝ) ≤ Real.atanh (Real.exp (-Real.log 5 / 4)) ∧
      Real.atanh (Real.exp (-Real.log 5 / 4)) ≤ ((logEnclosure.hi / 2 : ℚ) : ℝ) := by
  have h := IntervalRat.mem_logComputable ratio_mem (by decide +kernel) 220
  change (logEnclosure.lo : ℝ) ≤ _ ∧ _ ≤ (logEnclosure.hi : ℝ) at h
  simp only [Real.atanh]
  push_cast
  constructor <;> linarith [h.1, h.2]

theorem arctan_x_bounds :
    ((atanSum xLo (2 * 140) : ℚ) : ℝ) ≤ Real.arctan (Real.exp (-Real.log 5 / 4)) ∧
      Real.arctan (Real.exp (-Real.log 5 / 4)) ≤ ((atanSum xHi (2 * 140 + 1) : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := x_bounds
  obtain ⟨a1, -⟩ := arctan_bounds xLo xLo_check.1 (by
    have := xHi_check.2.2
    have : xLo < xHi := by decide +kernel
    linarith) 140
  obtain ⟨-, b2⟩ := arctan_bounds xHi (by
    have := xLo_check.1
    have : xLo < xHi := by decide +kernel
    linarith) xHi_check.2.2 140
  exact ⟨a1.trans (Real.arctan_strictMono.monotone hl),
    (Real.arctan_strictMono.monotone hh).trans b2⟩

def tailLo : ℚ := 279579531885990481596649998507874375651177341419462884103235230423927595124774085006554852356652210/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def tailHi : ℚ := 279579531885990481596649998507874375651177341419462884103235230423927595124774085006554852356652211/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem tail_finite_check :
    tailLo ≤ 2 * (logEnclosure.lo / 2 + atanSum xLo (2 * 140)) ∧
      2 * (logEnclosure.hi / 2 + atanSum xHi (2 * 140 + 1)) ≤ tailHi := by
  decide +kernel

theorem tail_bounds : (tailLo : ℝ) ≤ tailExpr ∧ tailExpr ≤ (tailHi : ℝ) := by
  obtain ⟨a1, a2⟩ := atanh_bounds
  obtain ⟨b1, b2⟩ := arctan_x_bounds
  have c1 : ((tailLo : ℚ) : ℝ) ≤ ((2 * (logEnclosure.lo / 2 + atanSum xLo (2 * 140)) : ℚ) : ℝ) := by
    exact_mod_cast tail_finite_check.1
  have c2 : ((2 * (logEnclosure.hi / 2 + atanSum xHi (2 * 140 + 1)) : ℚ) : ℝ) ≤ ((tailHi : ℚ) : ℝ) := by
    exact_mod_cast tail_finite_check.2
  push_cast at c1 c2 a1 a2 b1 b2
  unfold tailExpr
  constructor <;> linarith

theorem tail_width : tailHi - tailLo ≤ (1 : ℚ) / 10 ^ 95 := by decide +kernel

/-- LeanCert's `Real.atanh` agrees with Mathlib's `Real.artanh` on `[-1, 1]`. -/
theorem atanh_eq_artanh {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) : Real.atanh y = Real.artanh y := by
  rw [Real.artanh_eq_half_log hy]
  rfl

/-- `tailExpr` in the main-system shape `2*(artanh (exp (-b/2)) + arctan (exp (-b/2)))`, `b = log 5 / 2`. -/
theorem tailExpr_eq_T_tail_form :
    tailExpr = 2 * (Real.artanh (Real.exp (-(Real.log 5 / 2) / 2)) +
      Real.arctan (Real.exp (-(Real.log 5 / 2) / 2))) := by
  have he : -(Real.log 5 / 2) / 2 = -Real.log 5 / 4 := by ring
  have hx0 := Real.exp_pos (-Real.log 5 / 4)
  have hx1 : Real.exp (-Real.log 5 / 4) ≤ 1 := by
    have := x_bounds.2
    have : (xHi : ℝ) < 1 := by exact_mod_cast xHi_check.2.2
    linarith
  rw [he, tailExpr, atanh_eq_artanh ⟨by linarith, hx1⟩]

theorem tail_bounds_artanh :
    (tailLo : ℝ) ≤ 2 * (Real.artanh (Real.exp (-(Real.log 5 / 2) / 2)) +
        Real.arctan (Real.exp (-(Real.log 5 / 2) / 2))) ∧
      2 * (Real.artanh (Real.exp (-(Real.log 5 / 2) / 2)) +
        Real.arctan (Real.exp (-(Real.log 5 / 2) / 2))) ≤ (tailHi : ℝ) := by
  rw [← tailExpr_eq_T_tail_form]
  exact tail_bounds

end RHTailNumeric0471
