import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # 0504: fixed-point integer balls

A ball `b = (m, e) : ℤ × ℕ` at scale `S > 0` encloses `x` iff `|x − m/S| ≤ e/S`.
Operations (all kernel-cheap integer arithmetic): `add`, `neg`, `sub`, and `smul a d` = multiplication
by the rational `a/d` (`d > 0`) with floor rounding. Each has a general enclosure lemma.
 -/

namespace RHBall0504

abbrev Ball := ℤ × ℕ

def mem (S : ℕ) (x : ℝ) (b : Ball) : Prop := |x - (b.1 : ℝ) / S| ≤ (b.2 : ℝ) / S

def add (b c : Ball) : Ball := (b.1 + c.1, b.2 + c.2)
def neg (b : Ball) : Ball := (-b.1, b.2)
def sub (b c : Ball) : Ball := (b.1 - c.1, b.2 + c.2)
/-- Multiply by `a/d` (`d > 0`): floor of `m·a/d`, radius `⌈e·|a|/d⌉ + 1`. -/
def smul (a : ℤ) (d : ℕ) (b : Ball) : Ball := ((b.1 * a) / (d : ℤ), (b.2 * a.natAbs + d - 1) / d + 1)

lemma mem_zero (S : ℕ) (hS : 0 < S) {x : ℝ} : mem S x (0, 0) ↔ x = 0 := by
  unfold mem; simp [abs_nonpos_iff, sub_eq_zero]

lemma mem_add {S : ℕ} {x y : ℝ} {b c : Ball} (hx : mem S x b) (hy : mem S y c) :
    mem S (x + y) (add b c) := by
  unfold mem add at *
  push_cast
  have : x + y - ((b.1 : ℝ) + c.1) / S = (x - b.1 / S) + (y - c.1 / S) := by ring
  rw [this, add_div]
  exact (abs_add_le _ _).trans (add_le_add hx hy)

lemma mem_neg {S : ℕ} {x : ℝ} {b : Ball} (hx : mem S x b) : mem S (-x) (neg b) := by
  unfold mem neg at *
  push_cast
  have : -x - -(b.1 : ℝ) / S = -(x - b.1 / S) := by ring
  rw [this, abs_neg]; exact hx

lemma mem_sub {S : ℕ} {x y : ℝ} {b c : Ball} (hx : mem S x b) (hy : mem S y c) :
    mem S (x - y) (sub b c) := by
  have h := mem_add hx (mem_neg hy)
  unfold add neg at h; unfold sub
  simpa [sub_eq_add_neg] using h

lemma mem_smul {S : ℕ} (hS : 0 < S) (a : ℤ) {d : ℕ} (hd : 0 < d) {x : ℝ} {b : Ball}
    (hx : mem S x b) : mem S (x * a / d) (smul a d b) := by
  unfold mem smul at *
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set q : ℤ := (b.1 * a) / (d : ℤ)
  set r : ℤ := (b.1 * a) % (d : ℤ)
  have hqr : b.1 * a = (d : ℤ) * q + r := (Int.mul_ediv_add_emod _ _).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hd.ne')
  have hr1 : r < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
  have hqr' : (b.1 : ℝ) * a = d * q + r := by exact_mod_cast hqr
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℝ) < d := by exact_mod_cast hr1
  -- ceiling part
  have hceil : ((b.2 * a.natAbs : ℕ) : ℝ) / d ≤ (((b.2 * a.natAbs + d - 1) / d : ℕ) : ℝ) := by
    rw [div_le_iff₀ hd']
    have h1 := Nat.lt_div_mul_add (a := b.2 * a.natAbs + d - 1) hd
    have h2 : b.2 * a.natAbs ≤ (b.2 * a.natAbs + d - 1) / d * d := by omega
    exact_mod_cast h2
  have habs : |(a : ℝ)| = (a.natAbs : ℝ) := by
    have hz : ((a.natAbs : ℤ) : ℝ) = |(a : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
    rw [← hz]; rfl
  have key : x * a / d - (q : ℝ) / S = (x - b.1 / S) * a / d + (r : ℝ) / (d * S) := by
    field_simp
    linear_combination hqr'
  rw [key]
  have t1 : |(x - b.1 / S) * a / d| ≤ (b.2 : ℝ) / S * a.natAbs / d := by
    rw [abs_div, abs_mul, abs_of_pos hd', habs]
    gcongr
  have t2 : |(r : ℝ) / (d * S)| ≤ 1 / S := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hS']
    nlinarith
  have t3 : (b.2 : ℝ) / S * a.natAbs / d + 1 / S ≤
      ((((b.2 * a.natAbs + d - 1) / d + 1 : ℕ)) : ℝ) / S := by
    have e : (b.2 : ℝ) / S * a.natAbs / d + 1 / S = (((b.2 * a.natAbs : ℕ) : ℝ) / d + 1) / S := by
      push_cast; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hS'.le
    have : ((((b.2 * a.natAbs + d - 1) / d + 1 : ℕ)) : ℝ) = (((b.2 * a.natAbs + d - 1) / d : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [this]; linarith
  calc _ ≤ |(x - b.1 / S) * a / d| + |(r : ℝ) / (d * S)| := abs_add_le _ _
    _ ≤ (b.2 : ℝ) / S * a.natAbs / d + 1 / S := add_le_add t1 t2
    _ ≤ _ := t3

end RHBall0504

