import StepA1_G1
import ShiftBounds0484

namespace RHG1Adapter0484
open RHConditionalLog5 RHConcreteParameters RHWeilShift

theorem h0_eq : RHH0Numeric0472.h0Expr = RHWeilShift.h0 := rfl

theorem prime_eq : RHPrimeNumeric0470.primeExpr = RHPrimeShift.B_prime := rfl

theorem pole_eq : RHPoleNumeric0473.poleExpr = RHWeilShift.P_penalty := rfl

theorem tail_eq : RHTailNumeric0471.tailExpr = RHWeilShift.T_tail := by
  exact RHTailNumeric0471.tailExpr_eq_T_tail_form

theorem even_shift : concrete.shift false ≤ c_even := by
  have h := RHShiftNumeric0475.even_shift
  rw [RHShiftNumeric0475.evenExpr, h0_eq, tail_eq, prime_eq] at h
  exact h

theorem odd_shift : concrete.shift true ≤ c_odd := by
  have h := RHShiftNumeric0475.odd_shift
  rw [RHShiftNumeric0475.oddExpr, RHShiftNumeric0475.evenExpr,
    h0_eq, tail_eq, prime_eq, pole_eq] at h
  exact h

theorem g1 : G1 concrete :=
  RHStepA1G1.g1_of_discharged even_shift odd_shift
    (RHStepA1G1.tail_archimedean_bound false)
    (RHStepA1G1.tail_archimedean_bound true)
    (RHStepA1G1.tail_prime_bound_unconditional false)
    (RHStepA1G1.tail_prime_bound_unconditional true)

end RHG1Adapter0484
