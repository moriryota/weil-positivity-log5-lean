import BallVec0504

/-! # 0509: coarsening balls

`within b c r sh`: `|m − c·2^sh| + e ≤ r·2^sh`. If `x ∈ b` at scale `2^(p+sh)` and `within`, then
`x ∈ (c, r)` at scale `2^p`. `allWithin` checks a whole list of ball pairs. -/

namespace RHCoarse0509
open RHBall0504

def within (b : Ball) (c : ℤ) (r : ℕ) (sh : ℕ) : Bool :=
  decide (|b.1 - c * 2 ^ sh| + (b.2 : ℤ) ≤ (r : ℤ) * 2 ^ sh)

theorem mem_coarse {p sh : ℕ} {x : ℝ} {b : Ball} {c : ℤ} {r : ℕ}
    (hx : mem (2 ^ (p + sh)) x b) (hw : within b c r sh = true) : mem (2 ^ p) x (c, r) := by
  unfold within at hw
  have hw' := of_decide_eq_true hw
  unfold mem at *
  simp only at hx ⊢
  have hS : (0 : ℝ) < 2 ^ (p + sh) := by positivity
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hw'' : |(b.1 : ℝ) - c * 2 ^ sh| + b.2 ≤ r * 2 ^ sh := by exact_mod_cast hw'
  have e1 : (2 : ℝ) ^ (p + sh) = 2 ^ p * 2 ^ sh := pow_add _ _ _
  have e2 : (c : ℝ) / 2 ^ p = c * 2 ^ sh / 2 ^ (p + sh) := by rw [e1]; field_simp
  have e3 : (r : ℝ) / 2 ^ p = r * 2 ^ sh / 2 ^ (p + sh) := by rw [e1]; field_simp
  push_cast at hx ⊢
  rw [e2, e3]
  have t := abs_sub_le x ((b.1 : ℝ) / 2 ^ (p + sh)) (c * 2 ^ sh / 2 ^ (p + sh))
  have t2 : |(b.1 : ℝ) / 2 ^ (p + sh) - c * 2 ^ sh / 2 ^ (p + sh)| = |(b.1 : ℝ) - c * 2 ^ sh| / 2 ^ (p + sh) := by
    rw [← sub_div, abs_div, abs_of_pos hS]
  have t3 : (|(b.1 : ℝ) - c * 2 ^ sh| + b.2) / 2 ^ (p + sh) ≤ r * 2 ^ sh / 2 ^ (p + sh) :=
    div_le_div_of_nonneg_right hw'' hS.le
  rw [add_div] at t3
  linarith

/-- Check a list of ball pairs against a list of coarse pairs. -/
def allWithin (sh : ℕ) : List (Ball × Ball) → List ((ℤ × ℕ) × (ℤ × ℕ)) → Bool
  | a :: as, s :: ss => within a.1 s.1.1 s.1.2 sh && within a.2 s.2.1 s.2.2 sh && allWithin sh as ss
  | [], [] => true
  | _, _ => false

theorem allWithin_get (sh : ℕ) : ∀ (as : List (Ball × Ball)) (ss : List ((ℤ × ℕ) × (ℤ × ℕ))),
    allWithin sh as ss = true → ∀ k < as.length,
      within (as.getD k ((0,0),(0,0))).1 (ss.getD k ((0,0),(0,0))).1.1 (ss.getD k ((0,0),(0,0))).1.2 sh = true ∧
      within (as.getD k ((0,0),(0,0))).2 (ss.getD k ((0,0),(0,0))).2.1 (ss.getD k ((0,0),(0,0))).2.2 sh = true
  | a :: as, s :: ss, h, 0, _ => by
      simp only [allWithin, Bool.and_eq_true] at h
      simp [h.1.1, h.1.2]
  | a :: as, s :: ss, h, k + 1, hk => by
      simp only [allWithin, Bool.and_eq_true] at h
      simpa using allWithin_get sh as ss h.2 k (by simpa using hk)
  | [], _, _, k, hk => by simp at hk
  | _ :: _, [], h, _, _ => by simp [allWithin] at h

end RHCoarse0509

