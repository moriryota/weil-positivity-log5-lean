import TargetFormBinding
import ConditionalLog5
import ConcreteParameters
import ResidualMembership
import RealWeilShift
import WeilShiftBound
import PrimeShift
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Polynomial
open RHConditionalLog5 RHResidualMembership RHWeilColumnCandidate RHLog5Bridge
open RHConcreteParameters RHRealWeil RHWeilShift RH_LiteratureBridge

namespace RHPoleParity

/-- Unconditional vanishing of the Lebesgue integral of any odd function on ℝ. -/
theorem integral_of_odd (f : ℝ → ℝ) (hf : ∀ x, f (-x) = - f x) :
    ∫ x, f x = 0 := by
  have hmap : (volume : Measure ℝ).map (fun x => -x) = volume :=
    Measure.map_neg_eq_self volume
  have h_meas : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h_comp : ∫ x, f (-x) = ∫ x, f x := by
    have h1 := (h_meas.integral_map (μ := volume) f).symm
    rw [hmap] at h1
    exact h1
  have h_odd : (∫ x, f (-x)) = ∫ x, - f x := by
    congr 1; ext x; exact hf x
  rw [integral_neg] at h_odd
  linarith [h_comp, h_odd]

/-- Recurrence polynomial parity identity. -/
lemma recPoly_eval_neg (n : ℕ) (x : ℝ) :
    (recPoly n).eval (-x) = (-1 : ℝ)^n * (recPoly n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [recPoly]
  | one => simp [recPoly]
  | more n ih0 ih1 =>
      unfold recPoly
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      rw [ih0, ih1]
      have h1 : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
        rw [pow_add, sq]; ring
      have h2 : (-x) * ((-1 : ℝ) ^ (n + 1) * eval x (recPoly (n + 1))) =
          (-1 : ℝ) ^ (n + 2) * (x * eval x (recPoly (n + 1))) := by
        rw [pow_add, pow_one]; ring
      rw [h2, h1]; ring

lemma basisPoly_eval_neg (n : ℕ) (x : ℝ) :
    (basisPoly n).eval (-x) = (-1 : ℝ)^n * (basisPoly n).eval x := by
  dsimp [basisPoly]
  simp only [eval_mul, eval_C, recPoly_eval_neg]
  ring

lemma basisPoly_even (n : ℕ) (x : ℝ) :
    (basisPoly (2*n)).eval (-x) = (basisPoly (2*n)).eval x := by
  have h := basisPoly_eval_neg (2*n) x
  have hpow : (-1 : ℝ) ^ (2*n) = 1 := by
    rw [pow_mul, neg_one_sq, one_pow]
  rw [hpow, one_mul] at h
  exact h

lemma basisPoly_odd (n : ℕ) (x : ℝ) :
    (basisPoly (2*n+1)).eval (-x) = - (basisPoly (2*n+1)).eval x := by
  have h := basisPoly_eval_neg (2*n+1) x
  have hpow : (-1 : ℝ) ^ (2*n+1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  rw [hpow, neg_one_mul] at h
  exact h

lemma zeroPoly_neg_of_even (L : ℝ) (p : Polynomial ℝ) (hp : ∀ y, p.eval (-y) = p.eval y) (x : ℝ) :
    zeroPoly L p (-x) = zeroPoly L p x := by
  unfold zeroPoly Set.indicator
  have hmem : -x ∈ Set.Icc (-L) L ↔ x ∈ Set.Icc (-L) L := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith, by linarith⟩
  by_cases hx : x ∈ Set.Icc (-L) L
  · have hnx : -x ∈ Set.Icc (-L) L := hmem.mpr hx
    rw [if_pos hx, if_pos hnx]
    dsimp only
    exact hp x
  · have hnx : -x ∉ Set.Icc (-L) L := fun h => hx (hmem.mp h)
    rw [if_neg hx, if_neg hnx]

lemma basis_even (n : ℕ) (x : ℝ) :
    basis (2*n) (-x) = basis (2*n) x :=
  zeroPoly_neg_of_even halfWidth (basisPoly (2*n)) (basisPoly_even n) x

lemma low_even (u : ℝ → ℝ) (x : ℝ) :
    low false u (-x) = low false u x := by
  unfold low
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hd : degree false i = 2 * (i : ℕ) := rfl
  rw [hd, basis_even (i : ℕ) x]

lemma component_even (u : ℝ → ℝ) (x : ℝ) :
    component false u (-x) = component false u x := by
  unfold component
  dsimp
  ring

lemma tail_even (u : ℝ → ℝ) (x : ℝ) :
    tail false u (-x) = tail false u x := by
  unfold tail
  simp only [Pi.sub_apply]
  rw [component_even u x, low_even u x]

/-- The integrand  is strictly odd. -/
lemma tail_false_mul_sinh_odd (u : ℝ → ℝ) (x : ℝ) :
    tail false u (-x) * Real.sinh (-x / 2) = - (tail false u x * Real.sinh (x / 2)) := by
  rw [tail_even u x, neg_div, Real.sinh_neg, mul_neg]

/-- Vanishing of the sinh moment for the even sector tail. -/
theorem tail_false_sinh_integral_eq_zero (u : ℝ → ℝ) :
    ∫ x, tail false u x * Real.sinh (x / 2) = 0 :=
  integral_of_odd (fun x => tail false u x * Real.sinh (x / 2)) (tail_false_mul_sinh_odd u)

/-- Unconditional nonnegativity of the pole term in the even sector. -/
theorem hpole_even_unconditional (u : ℝ → ℝ) :
    0 ≤ 2 * (∫ x, tail false u x * Real.cosh (x / 2))^2 -
        2 * (∫ x, tail false u x * Real.sinh (x / 2))^2 := by
  rw [tail_false_sinh_integral_eq_zero u]
  ring_nf
  positivity

/-- Connection to Weil shift bound via Archimedean energy, prime, and pole forms (even sector). -/
theorem even_shift_of_analytic
    (h_shift_le : concrete.shift false ≤ c_even)
    (u : ℝ → ℝ) (_hu : Test u)
    (hE : compare (tail false u) + T_tail * (∫ x, (tail false u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail false u x - tail false u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail false u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail false u x)^2))
    (hpole : 0 ≤ 2*(∫ x, tail false u x * Real.cosh (x/2))^2 - 2*(∫ x, tail false u x * Real.sinh (x/2))^2) :
    compare (tail false u) + concrete.shift false * (∫ x, (tail false u x)^2) ≤ spatial_weil (tail false u) := by
  have h_weil := spatial_weil_shift_even (tail false u) (compare (tail false u)) hE hprime hpole
  have h_sq : 0 ≤ ∫ x, (tail false u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have h_order : concrete.shift false * (∫ x, (tail false u x)^2) ≤ c_even * (∫ x, (tail false u x)^2) :=
    mul_le_mul_of_nonneg_right h_shift_le h_sq
  linarith

/-- Connection to Weil shift bound via Archimedean energy, prime, and pole forms (odd sector). -/
theorem odd_shift_of_analytic
    (h_shift_le : concrete.shift true ≤ c_odd)
    (u : ℝ → ℝ) (_hu : Test u)
    (hE : compare (tail true u) + T_tail * (∫ x, (tail true u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail true u x - tail true u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail true u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail true u x)^2))
    (hpole : - P_penalty * (∫ x, (tail true u x)^2) ≤
      2*(∫ x, tail true u x * Real.cosh (x/2))^2 - 2*(∫ x, tail true u x * Real.sinh (x/2))^2) :
    compare (tail true u) + concrete.shift true * (∫ x, (tail true u x)^2) ≤ spatial_weil (tail true u) := by
  have h_weil := spatial_weil_shift_odd (tail true u) (compare (tail true u)) hE hprime hpole
  have h_sq : 0 ≤ ∫ x, (tail true u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have h_order : concrete.shift true * (∫ x, (tail true u x)^2) ≤ c_odd * (∫ x, (tail true u x)^2) :=
    mul_le_mul_of_nonneg_right h_shift_le h_sq
  linarith

/-- Discharged version of even_shift_of_analytic eliminating the hpole hypothesis completely. -/
theorem even_shift_of_analytic_discharged
    (h_shift_le : concrete.shift false ≤ c_even)
    (u : ℝ → ℝ) (hu : Test u)
    (hE : compare (tail false u) + T_tail * (∫ x, (tail false u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail false u x - tail false u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail false u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail false u x)^2)) :
    compare (tail false u) + concrete.shift false * (∫ x, (tail false u x)^2) ≤ spatial_weil (tail false u) :=
  even_shift_of_analytic h_shift_le u hu hE hprime (hpole_even_unconditional u)


lemma zeroPoly_neg_of_odd (L : ℝ) (p : Polynomial ℝ) (hp : ∀ y, p.eval (-y) = - p.eval y) (x : ℝ) :
    zeroPoly L p (-x) = - zeroPoly L p x := by
  unfold zeroPoly Set.indicator
  have hmem : -x ∈ Set.Icc (-L) L ↔ x ∈ Set.Icc (-L) L := by
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; refine ⟨by linarith, by linarith⟩
  by_cases hx : x ∈ Set.Icc (-L) L
  · have hnx : -x ∈ Set.Icc (-L) L := hmem.mpr hx
    rw [if_pos hx, if_pos hnx]
    dsimp only
    exact hp x
  · have hnx : -x ∉ Set.Icc (-L) L := fun h => hx (hmem.mp h)
    rw [if_neg hx, if_neg hnx, neg_zero]

lemma basis_odd (n : ℕ) (x : ℝ) :
    basis (2*n+1) (-x) = - basis (2*n+1) x :=
  zeroPoly_neg_of_odd halfWidth (basisPoly (2*n+1)) (basisPoly_odd n) x

lemma low_odd (u : ℝ → ℝ) (x : ℝ) :
    low true u (-x) = - low true u x := by
  unfold low
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd : degree true i = 2 * (i : ℕ) + 1 := rfl
  rw [hd, basis_odd (i : ℕ) x, mul_neg]

lemma component_odd (u : ℝ → ℝ) (x : ℝ) :
    component true u (-x) = - component true u x := by
  unfold component
  dsimp
  ring

lemma tail_odd (u : ℝ → ℝ) (x : ℝ) :
    tail true u (-x) = - tail true u x := by
  unfold tail
  simp only [Pi.sub_apply]
  rw [component_odd u x, low_odd u x]
  ring

/-- The integrand  is strictly odd. -/
lemma tail_true_mul_cosh_odd (u : ℝ → ℝ) (x : ℝ) :
    tail true u (-x) * Real.cosh (-x / 2) = - (tail true u x * Real.cosh (x / 2)) := by
  rw [tail_odd u x, neg_div, Real.cosh_neg, neg_mul]

/-- Vanishing of the cosh moment for the odd sector tail. -/
theorem tail_true_cosh_integral_eq_zero (u : ℝ → ℝ) :
    ∫ x, tail true u x * Real.cosh (x / 2) = 0 :=
  integral_of_odd (fun x => tail true u x * Real.cosh (x / 2)) (tail_true_mul_cosh_odd u)

/-- Exact reduction of the odd sector pole quadratic difference to pure sinh moment. -/
theorem odd_pole_eq_neg_sinh_sq (u : ℝ → ℝ) :
    2 * (∫ x, tail true u x * Real.cosh (x / 2))^2 -
      2 * (∫ x, tail true u x * Real.sinh (x / 2))^2 =
    - 2 * (∫ x, tail true u x * Real.sinh (x / 2))^2 := by
  rw [tail_true_cosh_integral_eq_zero u]
  ring

end RHPoleParity

