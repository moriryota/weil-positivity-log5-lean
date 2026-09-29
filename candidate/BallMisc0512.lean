import BallVec0504
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # 0512: ball utilities for the final assembly

* `mem_widen`: `mem S y (m,e)` and `|x − y| ≤ d ≤ e'/S` ⇒ `mem S x (m, e+e')`;
* `mem_of_sq_bounds`: a ball for `√a` from squared rational bounds;
* `bsum`: ball sum over a list, and its enclosure for `Finset.univ` sums over `Fin N`. -/

open Finset
open scoped BigOperators

namespace RHBallMisc0512
open RHBall0504

lemma mem_widen {S : ℕ} {x y d : ℝ} {m : ℤ} {e e' : ℕ} (hy : mem S y (m, e)) (hxy : |x - y| ≤ d)
    (hd : d ≤ (e' : ℝ) / S) : mem S x (m, e + e') := by
  unfold mem at *; simp only at *
  have := abs_sub_le x y ((m : ℝ) / S)
  push_cast; rw [add_div]; linarith

lemma mem_of_bounds' {S : ℕ} (hS : 0 < S) {x : ℝ} {m : ℤ} {e : ℕ}
    (hlo : ((m : ℝ) - e) / S ≤ x) (hhi : x ≤ ((m : ℝ) + e) / S) : mem S x (m, e) := by
  unfold mem; simp only
  rw [abs_le]; constructor
  · rw [sub_div] at hlo; linarith
  · rw [add_div] at hhi; linarith

/-- Ball for `√a`: if `lo² ≤ a ≤ hi²` with `0 ≤ lo`, then `lo ≤ √a ≤ hi`. -/
lemma sqrt_bounds {a lo hi : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ^ 2 ≤ a) (hhi : a ≤ hi ^ 2) (hhi0 : 0 ≤ hi) :
    lo ≤ Real.sqrt a ∧ Real.sqrt a ≤ hi := by
  constructor
  · rw [show lo = Real.sqrt (lo ^ 2) from (Real.sqrt_sq hlo0).symm]; exact Real.sqrt_le_sqrt hlo
  · rw [show hi = Real.sqrt (hi ^ 2) from (Real.sqrt_sq hhi0).symm]; exact Real.sqrt_le_sqrt hhi

def bsum : List Ball → Ball
  | [] => (0, 0)
  | b :: bs => add b (bsum bs)

theorem mem_bsum {S : ℕ} (hS : 0 < S) {N : ℕ} (f : Fin N → ℝ) (b : Fin N → Ball)
    (h : ∀ i, mem S (f i) (b i)) : mem S (∑ i, f i) (bsum (List.ofFn b)) := by
  induction N with
  | zero => simp [bsum, mem]
  | succ N ih =>
      rw [Fin.sum_univ_succ, List.ofFn_succ, bsum]
      exact mem_add (h 0) (ih (fun i => f i.succ) (fun i => b i.succ) (fun i => h i.succ))

end RHBallMisc0512

