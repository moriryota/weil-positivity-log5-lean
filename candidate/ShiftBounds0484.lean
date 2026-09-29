import FixedWeights
import H0Bounds0472
import PrimeNumeric0470
import TailBounds0471
import PoleBounds0473
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHShiftNumeric0475
open RHH0Numeric0472 RHPrimeNumeric0470 RHTailNumeric0471 RHPoleNumeric0473
noncomputable def evenExpr : ℝ := h0Expr + tailExpr - primeExpr
noncomputable def oddExpr : ℝ := evenExpr - poleExpr
theorem even_shift : RHFixedWeights.shift false ≤ evenExpr := by
  have hh := h0_bounds.1
  have ht := tail_bounds.1
  have hb := prime_bounds.2
  norm_num [h0Lo] at hh
  norm_num [tailLo] at ht
  norm_num [primeHi] at hb
  norm_num only [RHFixedWeights.shift, Bool.false_eq_true, ↓reduceIte]
  unfold evenExpr
  linarith
theorem odd_shift : RHFixedWeights.shift true ≤ oddExpr := by
  have hh := h0_bounds.1
  have ht := tail_bounds.1
  have hb := prime_bounds.2
  have hp := pole_bounds.2
  norm_num [h0Lo] at hh
  norm_num [tailLo] at ht
  norm_num [primeHi] at hb
  norm_num [poleHi] at hp
  norm_num only [RHFixedWeights.shift, ↓reduceIte]
  unfold oddExpr evenExpr
  linarith
theorem even_shift_artanh : RHFixedWeights.shift false ≤
    h0Expr + 2*(Real.artanh (Real.exp (-(Real.log 5/2)/2)) +
      Real.arctan (Real.exp (-(Real.log 5/2)/2))) - primeExpr := by
  rw [← tailExpr_eq_T_tail_form]
  exact even_shift
theorem odd_shift_artanh : RHFixedWeights.shift true ≤
    h0Expr + 2*(Real.artanh (Real.exp (-(Real.log 5/2)/2)) +
      Real.arctan (Real.exp (-(Real.log 5/2)/2))) - primeExpr - poleExpr := by
  rw [← tailExpr_eq_T_tail_form]
  exact odd_shift
end RHShiftNumeric0475
