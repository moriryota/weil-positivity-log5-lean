import RpExact0506
import RpCoef0506

/-! # 0510: Cc, Ss in Legendre form

`ξ j = XS^j δ_0` (so `u^j = evV (j+1) (ξ j) u`), `∫_{−1}^1 p_n u^j = 2/(2n+1)·ξ_j(n)`.
`Cc n = L c_n (Σ_{j<N, j even} (L/2)^j/j! · 2/(2n+1) ξ_j(n) + R)`, `|R| ≤ 2·(L/2)^N (N+1)/(N!·N)`;
`Ss` likewise with odd `j`. -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace RHCcSs0510
open RHConditionalLog5 RHLog5Bridge RHLeg0503 RHLegVec0503 RHSparse0504 RHIter0505 RHRpExact0506

noncomputable def ξ : ℕ → ℕ → ℝ
  | 0 => δ 0
  | j + 1 => XS (ξ j)

lemma ξ_supp : ∀ j l, j + 1 ≤ l → ξ j l = 0
  | 0, l, h => by simp [ξ, δ]; omega
  | j + 1, l, h => XS_zero (ξ_supp j) l (by omega)

lemma pow_evV : ∀ (j : ℕ) (u : ℝ), u ^ j = evV (j + 1) (ξ j) u
  | 0, u => by simp [evV, ξ, δ, p_zero]
  | j + 1, u => by rw [pow_succ, mul_comm, pow_evV j u, X_evS (ξ_supp j)]; rfl

lemma int_p_pow (n j : ℕ) : ∫ u in (-1:ℝ)..1, p n u * u ^ j = 2 / (2 * n + 1) * ξ j n := by
  have e : (fun u => p n u * u ^ j) = fun u => ∑ l ∈ range (j + 1), ξ j l * (p n u * p l u) := by
    funext u; rw [pow_evV, evV, mul_sum]; exact sum_congr rfl (fun l _ => by ring)
  rw [e, intervalIntegral.integral_finsetSum (f := fun l u => ξ j l * (p n u * p l u))
    (fun l _ => (continuous_const.mul ((continuous_p n).mul (continuous_p l))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, RHLink0505.orth]
  by_cases h : n < j + 1
  · rw [sum_eq_single n (fun l _ hl => by rw [if_neg (Ne.symm hl), mul_zero]) (fun h' => absurd (mem_range.mpr h) h'),
      if_pos rfl]; ring
  · rw [ξ_supp j n (by omega), sum_eq_zero (fun l hl => by simp at hl; rw [if_neg (by omega), mul_zero])]; ring

/-- Even/odd Taylor part of `exp` at `x`: `(Σ x^m/m! ± Σ (−x)^m/m!)/2`. -/
lemma exp_pair_bound {x : ℝ} (hx : |x| ≤ 1) (N : ℕ) (hN : 0 < N) :
    |Real.cosh x - ∑ m ∈ range N, (if m % 2 = 0 then x ^ m / m.factorial else 0)| ≤
        |x| ^ N * ((N.succ : ℝ) / (N.factorial * N)) ∧
    |Real.sinh x - ∑ m ∈ range N, (if m % 2 = 1 then x ^ m / m.factorial else 0)| ≤
        |x| ^ N * ((N.succ : ℝ) / (N.factorial * N)) := by
  have h1 := Real.exp_bound hx hN
  have h2 := Real.exp_bound (x := -x) (by rwa [abs_neg]) hN
  rw [abs_neg] at h2
  have ev : ∀ m : ℕ, (if m % 2 = 0 then x ^ m / m.factorial else 0) = (x ^ m / m.factorial + (-x) ^ m / m.factorial) / 2 := by
    intro m
    rcases Nat.even_or_odd m with he | ho
    · rw [if_pos (Nat.even_iff.mp he), he.neg_pow]; ring
    · rw [if_neg (by rw [Nat.odd_iff.mp ho]; omega), ho.neg_pow]; ring
  have od : ∀ m : ℕ, (if m % 2 = 1 then x ^ m / m.factorial else 0) = (x ^ m / m.factorial - (-x) ^ m / m.factorial) / 2 := by
    intro m
    rcases Nat.even_or_odd m with he | ho
    · rw [if_neg (by rw [Nat.even_iff.mp he]; omega), he.neg_pow]; ring
    · rw [if_pos (Nat.odd_iff.mp ho), ho.neg_pow]; ring
  simp_rw [ev, od]
  rw [← sum_div, ← sum_div, sum_add_distrib, sum_sub_distrib, Real.cosh_eq, Real.sinh_eq]
  constructor
  · have e : (Real.exp x + Real.exp (-x)) / 2 - ((∑ m ∈ range N, x ^ m / m.factorial) +
        ∑ m ∈ range N, (-x) ^ m / m.factorial) / 2 =
        ((Real.exp x - ∑ m ∈ range N, x ^ m / m.factorial) + (Real.exp (-x) - ∑ m ∈ range N, (-x) ^ m / m.factorial)) / 2 := by ring
    rw [e, abs_div, abs_two]
    have := abs_add_le (Real.exp x - ∑ m ∈ range N, x ^ m / m.factorial) (Real.exp (-x) - ∑ m ∈ range N, (-x) ^ m / m.factorial)
    rw [div_le_iff₀ (by norm_num)]; linarith
  · have e : (Real.exp x - Real.exp (-x)) / 2 - ((∑ m ∈ range N, x ^ m / m.factorial) -
        ∑ m ∈ range N, (-x) ^ m / m.factorial) / 2 =
        ((Real.exp x - ∑ m ∈ range N, x ^ m / m.factorial) - (Real.exp (-x) - ∑ m ∈ range N, (-x) ^ m / m.factorial)) / 2 := by ring
    rw [e, abs_div, abs_two]
    have := abs_sub (Real.exp x - ∑ m ∈ range N, x ^ m / m.factorial) (Real.exp (-x) - ∑ m ∈ range N, (-x) ^ m / m.factorial)
    rw [div_le_iff₀ (by norm_num)]; linarith

@[fun_prop] lemma cont_p' (n : ℕ) : Continuous fun x => p n x := continuous_p n

noncomputable def ce (N : ℕ) (odd : Bool) (n : ℕ) : ℝ :=
  ∑ m ∈ range N, (if m % 2 = (if odd then 1 else 0) then (halfWidth / 2) ^ m / m.factorial else 0) *
    (2 / (2 * n + 1) * ξ m n)

noncomputable def bnd (N : ℕ) : ℝ := 2 * ((halfWidth / 2) ^ N * ((N.succ : ℝ) / (N.factorial * N)))

/-- `∫_I b_n(y) f(y/2) dy = L c_n ∫_{−1}^1 p_n(u) f(Lu/2) du`. -/
lemma scale_hyp (n : ℕ) (f : ℝ → ℝ) :
    ∫ y in Icc (-halfWidth) halfWidth, (basisPoly n).eval y * f (y / 2) =
      halfWidth * cc n * ∫ u in (-1:ℝ)..1, p n u * f (halfWidth * u / 2) := by
  rw [set_scale]
  simp only [bscale]
  rw [mul_assoc]; congr 1
  rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring

theorem hyp_eq (n N : ℕ) (hN : 0 < N) (odd : Bool) :
    ∃ R : ℝ, |R| ≤ bnd N ∧
      ∫ y in Icc (-halfWidth) halfWidth, (basisPoly n).eval y *
        (if odd then Real.sinh (y / 2) else Real.cosh (y / 2)) =
      halfWidth * cc n * (ce N odd n + R) := by
  have hL := halfWidth_pos
  have hL1 : halfWidth / 2 ≤ 1 := by
    have h5 := RHEntry00Bounds0495.b_l5.2
    have : (RHEntry00Bounds0495.l5H : ℝ) ≤ 4 := by
      have : RHEntry00Bounds0495.l5H ≤ 4 := by decide +kernel
      exact_mod_cast this
    unfold halfWidth; linarith
  set f : ℝ → ℝ := fun x => if odd then Real.sinh x else Real.cosh x with hf
  set T : ℝ → ℝ := fun u => ∑ m ∈ range N, (if m % 2 = (if odd then 1 else 0) then (halfWidth * u / 2) ^ m / m.factorial else 0)
  have hsc := scale_hyp n f
  simp only [hf] at hsc
  refine ⟨(∫ u in (-1:ℝ)..1, p n u * f (halfWidth * u / 2)) - ce N odd n, ?_, ?_⟩
  · -- the truncation error
    have hT : ∫ u in (-1:ℝ)..1, p n u * T u = ce N odd n := by
      have e : (fun u => p n u * T u) = fun u => ∑ m ∈ range N,
          (if m % 2 = (if odd then 1 else 0) then (halfWidth / 2) ^ m / m.factorial else 0) * (p n u * u ^ m) := by
        funext u; simp only [T]; rw [mul_sum]
        exact sum_congr rfl (fun m _ => by split_ifs <;> ring)
      rw [e, intervalIntegral.integral_finsetSum (f := fun m u => (if m % 2 = (if odd then 1 else 0) then
          (halfWidth / 2) ^ m / m.factorial else 0) * (p n u * u ^ m))
        (fun m _ => (continuous_const.mul ((continuous_p n).mul (continuous_pow m))).intervalIntegrable _ _)]
      unfold ce
      exact sum_congr rfl (fun m _ => by rw [intervalIntegral.integral_const_mul, int_p_pow])
    have hTc : Continuous T := by
      simp only [T]
      exact continuous_finsetSum _ (fun m _ => by split_ifs <;> fun_prop)
    have hfc : Continuous fun u => f (halfWidth * u / 2) := by
      simp only [hf]; split_ifs <;> fun_prop
    rw [← hT, ← intervalIntegral.integral_sub (f := fun u => p n u * f (halfWidth * u / 2)) (g := fun u => p n u * T u)
      ((continuous_p n).mul hfc |>.intervalIntegrable _ _) ((continuous_p n).mul hTc |>.intervalIntegrable _ _)]
    have hB : Continuous fun u => |p n u| * ((halfWidth / 2) ^ N * ((N.succ : ℝ) / (N.factorial * N))) := by fun_prop
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -1) (b := 1)
      (f := fun u => p n u * f (halfWidth * u / 2) - p n u * T u)
      (g := fun u => |p n u| * ((halfWidth / 2) ^ N * ((N.succ : ℝ) / (N.factorial * N)))) (by norm_num)
      (Filter.Eventually.of_forall (fun u hu => by
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hx : |halfWidth * u / 2| ≤ halfWidth / 2 := by
          rw [abs_div, abs_mul, abs_of_pos hL, abs_two]
          have : |u| ≤ 1 := abs_le.mpr ⟨hu.1.le, hu.2⟩
          nlinarith
        have hx1 : |halfWidth * u / 2| ≤ 1 := hx.trans hL1
        obtain ⟨hc, hs⟩ := exp_pair_bound hx1 N hN
        have hp : |halfWidth * u / 2| ^ N ≤ (halfWidth / 2) ^ N := pow_le_pow_left₀ (abs_nonneg _) hx N
        have hk : (0:ℝ) ≤ (N.succ : ℝ) / (N.factorial * N) := by positivity
        simp only [hf, T]
        cases odd
        · simp only [Bool.false_eq_true, if_false] at hc ⊢
          exact hc.trans (mul_le_mul_of_nonneg_right hp hk)
        · simp only [if_true] at hs ⊢
          exact hs.trans (mul_le_mul_of_nonneg_right hp hk)))
      (hB.intervalIntegrable _ _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const] at h
    have h1 := RHRpCoef0506.abs1 n
    unfold bnd
    calc _ ≤ _ := h
      _ ≤ 2 * ((halfWidth / 2) ^ N * ((N.succ : ℝ) / (N.factorial * N))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  · rw [hsc]; cases odd <;> simp [hf] <;> ring

end RHCcSs0510

