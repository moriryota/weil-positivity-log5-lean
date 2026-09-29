import ConditionalLog5
import RealLowZero

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix
namespace RHTestRecPoly
open RHConditionalLog5 RHLog5Bridge RHResidualMembership RHRealLowZero

lemma recPoly_eval_neg (n : ℕ) (x : ℝ) :
    (recPoly n).eval (-x) = (-1 : ℝ)^n * (recPoly n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [recPoly, Polynomial.eval_one, pow_zero, one_mul]
  | one =>
    simp only [recPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, pow_one]
    ring
  | more n ih0 ih1 =>
    simp only [recPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    rw [ih0, ih1]
    have h1 : (-1 : ℝ)^(n + 1) = - ((-1 : ℝ)^n) := by
      rw [pow_add, pow_one, mul_neg, mul_one]
    have h2 : (-1 : ℝ)^(n + 2) = (-1 : ℝ)^n := by
      rw [pow_add, show (-1 : ℝ)^2 = 1 by ring, mul_one]
    rw [h1, h2]
    ring

lemma basisPoly_eval_neg (n : ℕ) (x : ℝ) :
    (basisPoly n).eval (-x) = (-1 : ℝ)^n * (basisPoly n).eval x := by
  simp only [basisPoly, Polynomial.eval_mul, Polynomial.eval_C, recPoly_eval_neg]
  ring

lemma mem_Icc_neg_iff {x L : ℝ} : -x ∈ Icc (-L) L ↔ x ∈ Icc (-L) L := by
  simp only [mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; refine ⟨by linarith, by linarith⟩

lemma basis_neg (n : ℕ) (x : ℝ) :
    basis n (-x) = (-1 : ℝ)^n * basis n x := by
  unfold basis RHWeilColumnCandidate.zeroPoly
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · have hnx : -x ∈ Icc (-halfWidth) halfWidth := mem_Icc_neg_iff.mpr hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hnx]
    exact basisPoly_eval_neg n x
  · have hnx : -x ∉ Icc (-halfWidth) halfWidth := fun h => hx (mem_Icc_neg_iff.mp h)
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnx, mul_zero]

lemma component_neg (o : Bool) (u : ℝ → ℝ) (x : ℝ) :
    component o u (-x) = (if o then (-1 : ℝ) else 1) * component o u x := by
  unfold component
  cases o <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_neg] <;> ring

lemma integral_neg_eq_self (f : ℝ → ℝ) :
    (∫ x, f (-x)) = ∫ x, f x := by
  have h := (measurableEmbedding_neg (α := ℝ)).integral_map (μ := volume) f
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  exact h.symm

lemma integral_eq_zero_of_odd (g : ℝ → ℝ) (hg : ∀ x, g (-x) = - g x) :
    (∫ x, g x) = 0 := by
  have h1 : (∫ x, g x) = ∫ x, g (-x) := (integral_neg_eq_self g).symm
  have h2 : (∫ x, g (-x)) = ∫ x, - g x := by
    congr 1; ext x; exact hg x
  have h3 : (∫ x, - g x) = - ∫ x, g x := integral_neg g
  have h : (∫ x, g x) = - (∫ x, g x) := by
    calc
      (∫ x, g x) = ∫ x, g (-x) := h1
      _ = ∫ x, - g x := h2
      _ = - ∫ x, g x := h3
  linarith

lemma degree_mod_two (o : Bool) (m : ℕ) : (degree o m) % 2 = (if o then 1 else 0) := by
  cases o
  · change (2 * m + 0) % 2 = 0
    omega
  · change (2 * m + 1) % 2 = 1
    omega

lemma sign_mul_parity (o : Bool) (n : ℕ) (h : n % 2 ≠ (if o then 1 else 0)) :
    (-1 : ℝ)^n * (if o then (-1 : ℝ) else 1) = -1 := by
  cases o
  · have hodd : n % 2 = 1 := by
      change n % 2 ≠ 0 at h
      omega
    have hpow : (-1 : ℝ)^n = -1 := by
      rw [← Nat.div_add_mod n 2, hodd, pow_add, pow_mul, show (-1 : ℝ)^2 = 1 by ring, one_pow, one_mul, pow_one]
    change (-1 : ℝ)^n * 1 = -1
    rw [hpow, mul_one]
  · have heven : n % 2 = 0 := by
      change n % 2 ≠ 1 at h
      omega
    have hpow : (-1 : ℝ)^n = 1 := by
      rw [← Nat.div_add_mod n 2, heven, add_zero, pow_mul, show (-1 : ℝ)^2 = 1 by ring, one_pow]
    change (-1 : ℝ)^n * (-1) = -1
    rw [hpow, one_mul]

lemma coeff_component_opposite_parity (o : Bool) (u : ℝ → ℝ) (n : ℕ)
    (h : n % 2 ≠ (if o then 1 else 0)) :
    coeff (component o u) n = 0 := by
  unfold coeff
  apply integral_eq_zero_of_odd
  intro x
  have hb := basis_neg n x
  have hc := component_neg o u x
  have hs := sign_mul_parity o n h
  calc
    basis n (-x) * component o u (-x) =
      ((-1 : ℝ)^n * basis n x) * ((if o then (-1 : ℝ) else 1) * component o u x) := by rw [hb, hc]
    _ = ((-1 : ℝ)^n * (if o then (-1 : ℝ) else 1)) * (basis n x * component o u x) := by ring
    _ = - (basis n x * component o u x) := by rw [hs, neg_one_mul]

lemma coeff_low_opposite_parity (o : Bool) (u : ℝ → ℝ) (n : ℕ)
    (h : n % 2 ≠ (if o then 1 else 0)) :
    coeff (low o u) n = 0 := by
  classical
  have hi (i : I) : Integrable (fun x => alpha o u i * (basis n x * basis (degree o i) x)) volume :=
    ((basis_memLp n).integrable_mul (basis_memLp (degree o i))).const_mul _
  have he (x : ℝ) : basis n x * low o u x =
      ∑ i : I, alpha o u i * (basis n x * basis (degree o i) x) := by
    simp only [low, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold coeff
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]
  change (∑ i : I, alpha o u i * coeff (basis (degree o i)) n) = 0
  have hne (i : I) : n ≠ degree o i := by
    intro h_eq
    have hd := degree_mod_two o i.val
    rw [h_eq, hd] at h
    exact h rfl
  have hz (i : I) : coeff (basis (degree o i)) n = 0 := by
    rw [coeff_basis]
    split_ifs with h_if
    · exact False.elim (hne i h_if)
    · rfl
  simp [hz]

lemma coeff_tail_opposite_parity (o : Bool) (u : ℝ → ℝ) (hu : Test u) (n : ℕ)
    (h : n % 2 ≠ (if o then 1 else 0)) :
    coeff (tail o u) n = 0 := by
  change coeff (component o u - low o u) n = 0
  rw [coeff_sub _ _ (RHG3RealEmbedding.component_memLp o u hu) (low_memLp o u),
      coeff_component_opposite_parity o u n h,
      coeff_low_opposite_parity o u n h,
      sub_zero]

lemma sum_range_two_mul (o : Bool) (M : ℕ) (F : ℕ → ℝ)
    (hz : ∀ k, (k % 2 ≠ (if o then 1 else 0)) → F k = 0) :
    (∑ k ∈ Finset.range (2 * M), F k) = ∑ n ∈ Finset.range M, F (degree o n) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2 : 2 * (M + 1) = 2 * M + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    cases o
    · have h_deg : degree false M = 2 * M := by unfold degree; rfl
      have h_odd : (2 * M + 1) % 2 ≠ (if false then 1 else 0) := by
        change (2 * M + 1) % 2 ≠ 0
        omega
      rw [hz (2 * M + 1) h_odd, add_zero, h_deg]
    · have h_deg : degree true M = 2 * M + 1 := by unfold degree; rfl
      have h_even : (2 * M) % 2 ≠ (if true then 1 else 0) := by
        change (2 * M) % 2 ≠ 1
        omega
      rw [hz (2 * M) h_even, add_zero, h_deg]

end RHTestRecPoly
