import BallVec0504

/-! # 0509: ball × ball multiplication and ball dot products

* `mulB S a b`: `m = ⌊m₁m₂/S⌋`, `e = ⌈((|m₁|+e₁)e₂ + |m₂|e₁)/S⌉ + 1`; encloses `x·y`.
* `dotB S as bs` (structural): encloses `Σ_{l<min} c_l d_l`.
* `wsum w i bs`: encloses `Σ_l c_l · num_{i+l}/den_{i+l}`. -/

open Finset
open scoped BigOperators

namespace RHBallDot0509
open RHBall0504 RHBallVec0504

def mulB (S : ℕ) (a b : Ball) : Ball :=
  ((a.1 * b.1) / (S : ℤ), (((a.1.natAbs + a.2) * b.2 + b.1.natAbs * a.2) + S - 1) / S + 1)

lemma mem_mulB {S : ℕ} (hS : 0 < S) {x y : ℝ} {a b : Ball} (hx : mem S x a) (hy : mem S y b) :
    mem S (x * y) (mulB S a b) := by
  unfold mem mulB at *
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  set q : ℤ := (a.1 * b.1) / (S : ℤ)
  set r : ℤ := (a.1 * b.1) % (S : ℤ)
  have hqr : a.1 * b.1 = (S : ℤ) * q + r := (Int.mul_ediv_add_emod _ _).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hS.ne')
  have hr1 : r < S := Int.emod_lt_of_pos _ (by exact_mod_cast hS)
  have hqr' : (a.1 : ℝ) * b.1 = S * q + r := by exact_mod_cast hqr
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℝ) < S := by exact_mod_cast hr1
  have ha1 : |(a.1 : ℝ)| = (a.1.natAbs : ℝ) := by
    have hz : ((a.1.natAbs : ℤ) : ℝ) = |(a.1 : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
    rw [← hz]; rfl
  have hb1 : |(b.1 : ℝ)| = (b.1.natAbs : ℝ) := by
    have hz : ((b.1.natAbs : ℤ) : ℝ) = |(b.1 : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
    rw [← hz]; rfl
  -- |x| ≤ (|m₁| + e₁)/S
  have hxabs : |x| ≤ ((a.1.natAbs : ℝ) + a.2) / S := by
    have := abs_sub_abs_le_abs_sub x ((a.1 : ℝ) / S)
    rw [abs_div, abs_of_pos hS', ha1] at this
    rw [add_div]; linarith
  set X := ((a.1.natAbs + a.2) * b.2 + b.1.natAbs * a.2 : ℕ)
  have hceil : (X : ℝ) / S ≤ (((X + S - 1) / S : ℕ) : ℝ) := by
    rw [div_le_iff₀ hS']
    have h1 := Nat.lt_div_mul_add (a := X + S - 1) hS
    have h2 : X ≤ (X + S - 1) / S * S := by omega
    exact_mod_cast h2
  have key : x * y - (q : ℝ) / S = x * (y - b.1 / S) + (b.1 / S) * (x - a.1 / S) + r / (S * S) := by
    field_simp
    linear_combination hqr'
  rw [key]
  have t1 : |x * (y - b.1 / S)| ≤ ((a.1.natAbs : ℝ) + a.2) / S * (b.2 / S) := by
    rw [abs_mul]; exact mul_le_mul hxabs hy (abs_nonneg _) (by positivity)
  have t2 : |(b.1 : ℝ) / S * (x - a.1 / S)| ≤ (b.1.natAbs : ℝ) / S * (a.2 / S) := by
    rw [abs_mul, abs_div, abs_of_pos hS', hb1]; exact mul_le_mul_of_nonneg_left hx (by positivity)
  have t3 : |(r : ℝ) / (S * S)| ≤ 1 / S := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hS']
    nlinarith
  have hX : ((a.1.natAbs : ℝ) + a.2) / S * (b.2 / S) + (b.1.natAbs : ℝ) / S * (a.2 / S) = (X : ℝ) / S / S := by
    simp only [X]; push_cast; field_simp
  calc |x * (y - b.1 / S) + (b.1 / S) * (x - a.1 / S) + r / (S * S)|
      ≤ |x * (y - b.1 / S)| + |(b.1 : ℝ) / S * (x - a.1 / S)| + |(r : ℝ) / (S * S)| := by
        have := abs_add_le (x * (y - b.1 / S) + (b.1 / S) * (x - a.1 / S)) (r / (S * S))
        have := abs_add_le (x * (y - b.1 / S)) ((b.1 / S) * (x - a.1 / S))
        linarith
    _ ≤ (X : ℝ) / S / S + 1 / S := by linarith
    _ ≤ (((X + S - 1) / S + 1 : ℕ) : ℝ) / S := by
        have e : (X : ℝ) / S / S + 1 / S = ((X : ℝ) / S + 1) / S := by field_simp
        rw [e]
        apply div_le_div_of_nonneg_right _ hS'.le
        push_cast; linarith

/-- Structural dot product. -/
def dotB (S : ℕ) : List Ball → List Ball → Ball
  | a :: as, b :: bs => add (mulB S a b) (dotB S as bs)
  | _, _ => (0, 0)

lemma vecMem_tail {S : ℕ} {c : ℕ → ℝ} {a : Ball} {as : List Ball} (h : VecMem S c (a :: as)) :
    VecMem S (fun l => c (l + 1)) as := fun l => by have := h (l + 1); simpa using this

theorem mem_dotB {S : ℕ} (hS : 0 < S) : ∀ (as bs : List Ball) (c d : ℕ → ℝ),
    VecMem S c as → VecMem S d bs → mem S (∑ l ∈ range (min as.length bs.length), c l * d l) (dotB S as bs)
  | a :: as, b :: bs, c, d, hc, hd => by
      have h0 := mem_mulB hS (by simpa using hc 0) (by simpa using hd 0)
      have ih := mem_dotB hS as bs (fun l => c (l + 1)) (fun l => d (l + 1)) (vecMem_tail hc) (vecMem_tail hd)
      simp only [List.length_cons, Nat.add_min_add_right, dotB]
      rw [sum_range_succ', add_comm]
      exact mem_add h0 ih
  | [], _, c, d, _, _ => by simp [dotB, mem]
  | _ :: _, [], c, d, _, _ => by simp [dotB, mem]

/-- Weighted sum with weights `w (i+l) = (num, den)`. -/
def wsum (w : ℕ → ℤ × ℕ) : ℕ → List Ball → Ball
  | _, [] => (0, 0)
  | i, b :: bs => add (smul (w i).1 (w i).2 b) (wsum w (i + 1) bs)

theorem mem_wsum {S : ℕ} (hS : 0 < S) (w : ℕ → ℤ × ℕ) (hw : ∀ i, 0 < (w i).2) :
    ∀ (i : ℕ) (bs : List Ball) (c : ℕ → ℝ), VecMem S c bs →
      mem S (∑ l ∈ range bs.length, c l * (w (i + l)).1 / (w (i + l)).2) (wsum w i bs)
  | i, [], c, _ => by simp [wsum, mem]
  | i, b :: bs, c, hc => by
      have h0 := mem_smul hS (w i).1 (hw i) (by simpa using hc 0)
      have ih := mem_wsum hS w hw (i + 1) bs (fun l => c (l + 1)) (vecMem_tail hc)
      simp only [List.length_cons, wsum]
      rw [sum_range_succ', add_comm]
      have e : ∑ l ∈ range bs.length, c (l + 1) * ((w (i + (l + 1))).1 : ℝ) / ((w (i + (l + 1))).2 : ℝ) =
          ∑ l ∈ range bs.length, c (l + 1) * ((w (i + 1 + l)).1 : ℝ) / ((w (i + 1 + l)).2 : ℝ) :=
        sum_congr rfl (fun l _ => by rw [show i + (l + 1) = i + 1 + l by ring])
      rw [e]
      simpa using mem_add h0 ih

end RHBallDot0509

