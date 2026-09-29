import LegendreContract

namespace RHLegendreContract
lemma Q_zero_base : Q 0 = 1 := by
  norm_num [Q, Polynomial.shiftedLegendre, Finset.sum_range_succ]
lemma Q_one_base : Q 1 = 1-Polynomial.C 2*Polynomial.X := by
  norm_num [Q, Polynomial.shiftedLegendre, Finset.sum_range_succ]
  simp only [Polynomial.C_ofNat]
  ring
end RHLegendreContract
