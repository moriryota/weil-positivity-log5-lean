import PrRed0511

/-! # 0522: polynomials of degree ≤ 127 in the basis `basisPoly l`, and their parity parts

* `poly_basis`: `P.eval x = Σ_{l<128} c_l · (basisPoly l).eval x` for `natDegree P ≤ 127`;
* `poly_parity`: `(P(x) + (−1)^o P(−x))/2 = Σ_{m<64} c_m · (basisPoly (degree o m)).eval x`.
 -/

open Finset
open scoped BigOperators

namespace RHPolyExp0522
open RHLeg0503 RHLegVec0503 RHConditionalLog5 RHLog5Bridge

lemma mono_evV : ∀ j : ℕ, ∃ c : ℕ → ℝ, ∀ u : ℝ, u ^ j = evV (j + 1) c u
  | 0 => ⟨fun l => if l = 0 then 1 else 0, fun u => by simp [evV, p_zero]⟩
  | j + 1 => by
    obtain ⟨c, hc⟩ := mono_evV j
    exact ⟨XV (j + 1) c, fun u => by rw [pow_succ, mul_comm, hc u, X_evV]⟩

lemma evV_pad {N M : ℕ} (h : N ≤ M) (c : ℕ → ℝ) (u : ℝ) :
    evV N c u = evV M (fun l => if l < N then c l else 0) u := by
  unfold evV
  rw [← sum_subset (range_subset_range.mpr h) (fun l _ hl => by simp at hl; simp [show ¬ l < N by omega])]
  exact sum_congr rfl (fun l hl => by simp at hl; simp [hl])

lemma mono_128 {j : ℕ} (hj : j ≤ 127) : ∃ c : ℕ → ℝ, ∀ u : ℝ, u ^ j = ∑ l ∈ range 128, c l * p l u := by
  obtain ⟨c, hc⟩ := mono_evV j
  exact ⟨_, fun u => by rw [hc u, evV_pad (by omega : j + 1 ≤ 128)]; rfl⟩

theorem poly_u (P : Polynomial ℝ) (hP : P.natDegree ≤ 127) :
    ∃ C : ℕ → ℝ, ∀ x, P.eval x = ∑ l ∈ range 128, C l * p l (x / halfWidth) := by
  have hL := halfWidth_pos
  choose c hc using fun j : Fin 128 => mono_128 (j := j.val) (by omega)
  refine ⟨fun l => ∑ j : Fin 128, P.coeff j * halfWidth ^ (j : ℕ) * c j l, fun x => ?_⟩
  rw [Polynomial.eval_eq_sum_range' (n := 128) (by omega)]
  have e : ∀ j ∈ range 128, P.coeff j * x ^ j =
      ∑ l ∈ range 128, P.coeff j * halfWidth ^ j * (if h : j < 128 then c ⟨j, h⟩ l else 0) * p l (x / halfWidth) := by
    intro j hj
    have hj' : j < 128 := mem_range.mp hj
    have hx : x = halfWidth * (x / halfWidth) := by field_simp
    rw [hx, mul_pow, show (halfWidth * (x / halfWidth) / halfWidth) = x / halfWidth by field_simp]
    rw [hc ⟨j, hj'⟩ (x / halfWidth), mul_sum, mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    simp only [hj', dite_true]; ring
  rw [sum_congr rfl e, sum_comm]
  refine sum_congr rfl (fun l _ => ?_)
  rw [← sum_mul]
  congr 1

lemma cc_pos (l : ℕ) : 0 < RHRpExact0506.cc l := by
  unfold RHRpExact0506.cc
  apply Real.sqrt_pos.mpr
  have := halfWidth_pos
  positivity

theorem poly_basis (P : Polynomial ℝ) (hP : P.natDegree ≤ 127) :
    ∃ c : ℕ → ℝ, ∀ x, P.eval x = ∑ l ∈ range 128, c l * (basisPoly l).eval x := by
  obtain ⟨C, hC⟩ := poly_u P hP
  refine ⟨fun l => C l / RHRpExact0506.cc l, fun x => ?_⟩
  rw [hC x]
  refine sum_congr rfl (fun l _ => ?_)
  rw [RHLink0505.basisPoly_eval]
  have h := (cc_pos l).ne'
  change C l * p l (x / halfWidth) = C l / RHRpExact0506.cc l * (RHRpExact0506.cc l * p l (x / halfWidth))
  field_simp

lemma sum_even_odd (f : ℕ → ℝ) : ∀ n, ∑ l ∈ range (2 * n), f l = ∑ m ∈ range n, (f (2 * m) + f (2 * m + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_even_odd f n, sum_range_succ]
    ring

theorem poly_parity (P : Polynomial ℝ) (hP : P.natDegree ≤ 127) (o : Bool) :
    ∃ c : ℕ → ℝ, ∀ x, (P.eval x + (-1) ^ (if o then 1 else 0) * P.eval (-x)) / 2 =
      ∑ m ∈ range 64, c m * (basisPoly (degree o m)).eval x := by
  obtain ⟨c, hc⟩ := poly_basis P hP
  refine ⟨fun m => c (degree o m), fun x => ?_⟩
  rw [hc x, hc (-x)]
  simp only [RHPrRed0511.bparity]
  rw [mul_sum, ← sum_add_distrib, sum_div, show (128 : ℕ) = 2 * 64 by norm_num, sum_even_odd]
  refine sum_congr rfl (fun m _ => ?_)
  unfold degree
  cases o <;> simp [pow_add, pow_mul] <;> ring

end RHPolyExp0522

