import Constants0467
import Log2_100
open LeanCert.Core
namespace RHPrimeNumeric0470
/-- Widening is checked over rationals, then transported to the real interval. -/
theorem widen {I J : IntervalRat} {x : ℝ}
    (h : J.lo ≤ I.lo ∧ I.hi ≤ J.hi) (hx : x ∈ I) : x ∈ J := by
  exact ⟨le_trans (by exact_mod_cast h.1) hx.1,
    le_trans hx.2 (by exact_mod_cast h.2)⟩
def posInv (I : IntervalRat) (h : 0 < I.lo) : IntervalRat :=
  IntervalRat.invNonzero ⟨I, by intro hz; exact (not_le_of_gt h) hz.1⟩
theorem positive_of_mem {I : IntervalRat} {x : ℝ} (h : 0 < I.lo) (hx : x ∈ I) : 0 < x :=
  lt_of_lt_of_le (by exact_mod_cast h) hx.1
theorem mem_posInv {I : IntervalRat} {x : ℝ} (h : 0 < I.lo) (hx : x ∈ I) :
    x⁻¹ ∈ posInv I h :=
  IntervalRat.mem_invNonzero hx (ne_of_gt (positive_of_mem h hx))
def posDiv (I J : IntervalRat) (h : 0 < J.lo) : IntervalRat := I.mul (posInv J h)
theorem mem_posDiv {I J : IntervalRat} {x y : ℝ}
    (h : 0 < J.lo) (hx : x ∈ I) (hy : y ∈ J) : x / y ∈ posDiv I J h := by
  simpa only [div_eq_mul_inv, posDiv] using IntervalRat.mem_mul hx (mem_posInv h hy)
end RHPrimeNumeric0470
