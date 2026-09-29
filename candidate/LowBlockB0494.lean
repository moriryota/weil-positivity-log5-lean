import LowBlockA0494
import Caps0494

/-! # 0494 T1 step B: low-block matrix form and the finite-dimensional reduction of `G5c`

* `column` is linear in the polynomial.
* `targetQ_real (low o u) = ∑ i, ∑ j, α_i α_j A0true o i j` with
  `A0true o i j = ∫ col o j · basis (degree o i)`.
* `G5c concrete k` follows from a statement about `c : Fin 32 → ℝ` only.
 -/

open MeasureTheory Set
open scoped BigOperators Matrix

namespace RHLowBlock0494
open RHConditionalLog5 RHLog5Bridge RHWeilColumnCandidate RHTargetFormBinding RHResidualMembership

local notation "Kk" => RH_GammaFinalFormula.K_kernel

lemma zeroPoly_add (p q : Polynomial ℝ) (z : ℝ) :
    zeroPoly halfWidth (p + q) z = zeroPoly halfWidth p z + zeroPoly halfWidth q z := by
  by_cases hz : z ∈ Icc (-halfWidth) halfWidth <;> simp [zeroPoly, hz]

lemma zeroPoly_C_mul (a : ℝ) (p : Polynomial ℝ) (z : ℝ) :
    zeroPoly halfWidth (Polynomial.C a * p) z = a * zeroPoly halfWidth p z := by
  by_cases hz : z ∈ Icc (-halfWidth) halfWidth <;> simp [zeroPoly, hz]

lemma kernel_int (p : Polynomial ℝ) {x : ℝ} (hx : |x| < halfWidth) :
    IntegrableOn (fun y => Kk |x - y| * (p.eval x - p.eval y)) (Icc (-halfWidth) halfWidth) :=
  RHColL2.kernel_eval_sub_integrableOn halfWidth halfWidth_pos.le p x (abs_le.mp hx.le)

lemma poly_mul_int (p : Polynomial ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun y => p.eval y * g y) (Icc (-halfWidth) halfWidth) :=
  (p.continuous.mul hg).integrableOn_Icc

private noncomputable abbrev cn (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n

lemma prime_add (p q : Polynomial ℝ) (x : ℝ) :
    (∑ n ∈ Finset.range 5, cn n * (zeroPoly halfWidth (p + q) (x - Real.log n) +
      zeroPoly halfWidth (p + q) (x + Real.log n))) =
    (∑ n ∈ Finset.range 5, cn n * (zeroPoly halfWidth p (x - Real.log n) + zeroPoly halfWidth p (x + Real.log n))) +
    (∑ n ∈ Finset.range 5, cn n * (zeroPoly halfWidth q (x - Real.log n) + zeroPoly halfWidth q (x + Real.log n))) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [zeroPoly_add, zeroPoly_add]
  ring

lemma prime_C_mul (a : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    (∑ n ∈ Finset.range 5, cn n * (zeroPoly halfWidth (Polynomial.C a * p) (x - Real.log n) +
      zeroPoly halfWidth (Polynomial.C a * p) (x + Real.log n))) =
    a * ∑ n ∈ Finset.range 5, cn n * (zeroPoly halfWidth p (x - Real.log n) + zeroPoly halfWidth p (x + Real.log n)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [zeroPoly_C_mul, zeroPoly_C_mul]
  ring

lemma column_add (p q : Polynomial ℝ) (x : ℝ) :
    column halfWidth (p + q) x = column halfWidth p x + column halfWidth q x := by
  unfold column
  split_ifs with hx
  · have i1 : (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * ((p + q).eval x - (p + q).eval y)) =
        (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (p.eval x - p.eval y)) +
        (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (q.eval x - q.eval y)) := by
      rw [← integral_add (kernel_int p hx) (kernel_int q hx)]
      congr 1; funext y; simp only [Polynomial.eval_add]; ring
    have i2 : (∫ y in Icc (-halfWidth) halfWidth, (p + q).eval y * Real.cosh (y/2)) =
        (∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.cosh (y/2)) +
        (∫ y in Icc (-halfWidth) halfWidth, q.eval y * Real.cosh (y/2)) := by
      have hc : Continuous (fun y : ℝ => Real.cosh (y/2)) :=
        Real.continuous_cosh.comp (continuous_id.div_const 2)
      rw [← integral_add (poly_mul_int p hc) (poly_mul_int q hc)]
      congr 1; funext y; simp only [Polynomial.eval_add]; ring
    have i3 : (∫ y in Icc (-halfWidth) halfWidth, (p + q).eval y * Real.sinh (y/2)) =
        (∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.sinh (y/2)) +
        (∫ y in Icc (-halfWidth) halfWidth, q.eval y * Real.sinh (y/2)) := by
      have hc : Continuous (fun y : ℝ => Real.sinh (y/2)) :=
        Real.continuous_sinh.comp (continuous_id.div_const 2)
      rw [← integral_add (poly_mul_int p hc) (poly_mul_int q hc)]
      congr 1; funext y; simp only [Polynomial.eval_add]; ring
    rw [i1, i2, i3, prime_add, Polynomial.eval_add]
    ring
  · simp

lemma column_C_mul (a : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    column halfWidth (Polynomial.C a * p) x = a * column halfWidth p x := by
  unfold column
  split_ifs with hx
  · have i1 : (∫ y in Icc (-halfWidth) halfWidth,
          Kk |x - y| * ((Polynomial.C a * p).eval x - (Polynomial.C a * p).eval y)) =
        a * ∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (p.eval x - p.eval y) := by
      rw [← integral_const_mul]
      congr 1; funext y; simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring
    have i2 : (∫ y in Icc (-halfWidth) halfWidth, (Polynomial.C a * p).eval y * Real.cosh (y/2)) =
        a * ∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.cosh (y/2) := by
      rw [← integral_const_mul]
      congr 1; funext y; simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring
    have i3 : (∫ y in Icc (-halfWidth) halfWidth, (Polynomial.C a * p).eval y * Real.sinh (y/2)) =
        a * ∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.sinh (y/2) := by
      rw [← integral_const_mul]
      congr 1; funext y; simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring
    rw [i1, i2, i3, prime_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · simp

lemma column_zero (x : ℝ) : column halfWidth 0 x = 0 := by
  unfold column
  split_ifs <;> simp [zeroPoly]

lemma column_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (a : ι → ℝ) (x : ℝ) :
    column halfWidth (∑ j ∈ s, Polynomial.C (a j) * P j) x = ∑ j ∈ s, a j * column halfWidth (P j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [column_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, column_add, column_C_mul, ih]

lemma low_eq_zp (o : Bool) (u : ℝ → ℝ) : low o u = zp (RHSpatialDensity0490.lowPR o u) := by
  funext x
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · rw [RHSpatialDensity0490.low_eq_lowPR o u x hx, zp_of_mem _ hx]
  · rw [low_zero_outside o u x hx, zp_of_not_mem _ hx]

/-- Low-block matrix of the target form: `A0true o i j = ∫ col o j · basis (degree o i)`. -/
noncomputable def A0true (o : Bool) (i j : I) : ℝ := ∫ x, col o j x * basis (degree o i) x

/-- Mixed (band) matrix: `mixed o u i = ∑ j, α_j * Attrue o i j` by definition. -/
noncomputable def Attrue (o : Bool) (i j : I) : ℝ := ∫ x, col o j x * basis (degree o (32 + i)) x

lemma mixed_eq (o : Bool) (u : ℝ → ℝ) (i : I) : mixed o u i = ∑ j : I, alpha o u j * Attrue o i j := rfl

theorem targetQ_low_eq (o : Bool) (u : ℝ → ℝ) :
    targetQ_real (low o u) = ∑ i : I, ∑ j : I, alpha o u i * alpha o u j * A0true o i j := by
  have hcolL2 : ∀ j : I, MemLp (col o j) 2 volume := fun j => (RHG2Final0489.g2.1 o j).1
  have hint : ∀ i j : I, Integrable (fun x => col o j x * basis (degree o i) x) :=
    fun i j => (hcolL2 j).integrable_mul (basis_memLp (degree o i))
  rw [low_eq_zp o u, targetQ_zp]
  have hpt : (fun x => column halfWidth (RHSpatialDensity0490.lowPR o u) x *
      zp (RHSpatialDensity0490.lowPR o u) x) = fun x => ∑ i : I, ∑ j : I,
        alpha o u i * alpha o u j * (col o j x * basis (degree o i) x) := by
    funext x
    have hc : column halfWidth (RHSpatialDensity0490.lowPR o u) x =
        ∑ j : I, alpha o u j * col o j x := by
      unfold RHSpatialDensity0490.lowPR
      rw [column_sum]
      rfl
    have hz : zp (RHSpatialDensity0490.lowPR o u) x = ∑ i : I, alpha o u i * basis (degree o i) x := by
      rw [← low_eq_zp]
      simp [low, Finset.sum_apply]
    rw [hc, hz, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hpt, integral_finsetSum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hint i j).const_mul _))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  apply Finset.sum_congr rfl; intro j _
  rw [integral_const_mul]
  rfl

/-- The low-block Schur form as a function of the Legendre coefficient vector. -/
noncomputable def lowForm (o : Bool) (a : I → ℝ) : ℝ :=
  (∑ i : I, ∑ j : I, a i * a j * A0true o i j) -
    ∑ i : I, (∑ j : I, a j * Attrue o i j)^2 / RHConcreteParameters.concrete.weights o i

/-- **Finite-dimensional reduction of G5.** A lower bound for the fixed 32×32 form
`c ↦ lowForm o (B o *ᵥ c)` on all of `ℝ^32` implies `G5c concrete k`. -/
theorem G5c_of_lowForm (k : RHCaps0494.Caps)
    (h : ∀ (o : Bool) (c : I → ℝ),
      (1 - k.eta o) * (∑ i : I, (c i)^2) ≤ lowForm o (RHConcreteParameters.concrete.B o *ᵥ c)) :
    RHCaps0494.G5c RHConcreteParameters.concrete k := by
  intro o u _hu
  have hc := h o (RHConcreteParameters.concrete.coordinates o u)
  rw [RHConcreteParameters.coordinates_identity o u] at hc
  rw [targetQ_low_eq]
  simp only [mixed_eq]
  exact hc

end RHLowBlock0494

