import TuckLinear
open Polynomial
namespace RHTuckPreserves

theorem degree_le (p : Polynomial ℂ) :
    (RHTuckLinear.operator p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [degree_eq_natDegree hp]
    exact degree_le_of_natDegree_le (RHTuckLinear.natDegree_operator_le p)

theorem low_degree {p : Polynomial ℂ} {n : ℕ} (hp : p.degree < (n:ℕ)) :
    (RHTuckLinear.operator p).degree < (n:ℕ) :=
  lt_of_le_of_lt (degree_le p) hp
end RHTuckPreserves
