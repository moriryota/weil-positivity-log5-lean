import Nu0514
import Kappa0514
import Dilog0514

/-! # 0514: closed forms of the second-order log moments

With `μ_m = ∫ log(1+x) P_m` (0508), `H_n = Σ_{k<n} 1/(k+1)`,
`A_m = ∫ log(1+x)(x−1)P'_m`, `B_m = ∫ log(1+x)(x+1)P'_m`, `C_m = ∫ log(1−x)(x−1)P'_m`:
* `A_{m+2} = A_m + (m+2)μ_{m+2} + (m+1)μ_m − (2m+3)μ_{m+1}` (and the `+` version for `B`),
  from `P'_{m+2} − P'_m = (2m+3)P_{m+1}` and `(2m+3) x P_{m+1} = (m+2)P_{m+2} + (m+1)P_m`;
* `A_{m+1} = 2(−1)^{m+1}(log 2 − H_m − H_{m+2})`, `B_{m+1} = 2 log 2 − μ_{m+1}`, `C_m = (−1)^m B_m`;
* `ν_{n+1} = ∫ log²(1+x) P_{n+1} = μ_{n+1}(2 log 2 − 2H_n − 2H_{n+2})`,
* `κ_{n+1} = ∫ log(1+x)log(1−x) P_{n+1} = −((−1)^{n+1}+1)(2 log 2 − μ_{n+1})/((n+1)(n+2))`.
 -/

open Set intervalIntegral Real

namespace RHNuK0514
open RHLeg0503 RHLogMoment0508

/-- closed form of `μ_l` (0508 `mu_zero`, `mu_succ`) -/
noncomputable def muC : ℕ → ℝ
  | 0 => 2 * Real.log 2 - 2
  | n + 1 => 2 * (-1) ^ (n + 2) / (((n:ℝ) + 1) * ((n:ℝ) + 2))

lemma mu_eq : ∀ l : ℕ, ∫ x in (-1:ℝ)..1, Real.log (1 + x) * p l x = muC l
  | 0 => by rw [mu_zero]; rfl
  | n + 1 => by rw [mu_succ]; simp only [muC]

noncomputable def H (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / ((k:ℝ) + 1)

noncomputable def A (m : ℕ) : ℝ := ∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x - 1) * d m x)
noncomputable def B (m : ℕ) : ℝ := ∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x + 1) * d m x)
noncomputable def C (m : ℕ) : ℝ := ∫ x in (-1:ℝ)..1, Real.log (1 - x) * ((x - 1) * d m x)

lemma hi (l : ℕ) : IntervalIntegrable (fun x => Real.log (1 + x) * p l x) MeasureTheory.volume (-1) 1 :=
  log1p_ii.mul_continuousOn (continuous_p l).continuousOn

lemma hiA (m : ℕ) (c : ℝ) :
    IntervalIntegrable (fun x => Real.log (1 + x) * ((x + c) * d m x)) MeasureTheory.volume (-1) 1 :=
  log1p_ii.mul_continuousOn ((continuous_id.add continuous_const).mul (RHKappa0514.dcont m)).continuousOn

lemma rec_gen (m : ℕ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x + s) * d (m + 2) x) =
      (∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x + s) * d m x)) +
        ((m:ℝ) + 2) * muC (m + 2) + ((m:ℝ) + 1) * muC m + s * (2 * (m:ℝ) + 3) * muC (m + 1) := by
  have hc : (2 * (m:ℝ) + 3) ≠ 0 := by positivity
  have e : ∀ x, Real.log (1 + x) * ((x + s) * d (m + 2) x) =
      Real.log (1 + x) * ((x + s) * d m x) + ((m:ℝ) + 2) * (Real.log (1 + x) * p (m + 2) x) +
        ((m:ℝ) + 1) * (Real.log (1 + x) * p m x) + s * (2 * (m:ℝ) + 3) * (Real.log (1 + x) * p (m + 1) x) := by
    intro x
    have h1 := d_diff m x
    have h2 := x_mul_succ m x
    rw [eq_div_iff hc] at h2
    linear_combination (Real.log (1 + x) * (x + s)) * h1 + Real.log (1 + x) * h2
  simp only [e]
  rw [integral_add (((hiA m s).add ((hi _).const_mul _)).add ((hi _).const_mul _)) ((hi _).const_mul _),
    integral_add ((hiA m s).add ((hi _).const_mul _)) ((hi _).const_mul _),
    integral_add (hiA m s) ((hi _).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, mu_eq, mu_eq, mu_eq]

lemma A_rec (m : ℕ) : A (m + 2) =
    A m + ((m:ℝ) + 2) * muC (m + 2) + ((m:ℝ) + 1) * muC m - (2 * (m:ℝ) + 3) * muC (m + 1) := by
  have h := rec_gen m (-1) (Or.inr rfl)
  simp only [← sub_eq_add_neg] at h
  unfold A; rw [h]; ring

lemma B_rec (m : ℕ) : B (m + 2) =
    B m + ((m:ℝ) + 2) * muC (m + 2) + ((m:ℝ) + 1) * muC m + (2 * (m:ℝ) + 3) * muC (m + 1) := by
  have h := rec_gen m 1 (Or.inl rfl)
  unfold B; rw [h]; ring

lemma A_zero : A 0 = 0 := by simp [A, d_zero]
lemma B_zero : B 0 = 0 := by simp [B, d_zero]

lemma A_one : A 1 = muC 1 - muC 0 := by
  have e : ∀ x : ℝ, Real.log (1 + x) * ((x - 1) * d 1 x) = Real.log (1 + x) * p 1 x - Real.log (1 + x) * p 0 x := by
    intro x; rw [d_one, p_one, p_zero]; ring
  unfold A; simp only [e]; rw [integral_sub (hi 1) (hi 0), mu_eq, mu_eq]

lemma B_one : B 1 = muC 1 + muC 0 := by
  have e : ∀ x : ℝ, Real.log (1 + x) * ((x + 1) * d 1 x) = Real.log (1 + x) * p 1 x + Real.log (1 + x) * p 0 x := by
    intro x; rw [d_one, p_one, p_zero]; ring
  unfold B; simp only [e]; rw [integral_add (hi 1) (hi 0), mu_eq, mu_eq]

lemma H_succ (n : ℕ) : H (n + 1) = H n + 1 / ((n:ℝ) + 1) := by
  simp [H, Finset.sum_range_succ]

theorem A_closed : ∀ m : ℕ, A (m + 1) = 2 * (-1) ^ (m + 1) * (Real.log 2 - H m - H (m + 2)) ∧
    A (m + 2) = 2 * (-1) ^ (m + 2) * (Real.log 2 - H (m + 1) - H (m + 3))
  | 0 => by
    refine ⟨?_, ?_⟩
    · rw [A_one]; simp [muC, H, Finset.sum_range_succ]; ring
    · rw [A_rec 0, A_zero]; simp [muC, H, Finset.sum_range_succ]; ring
  | m + 1 => by
    obtain ⟨h1, h2⟩ := A_closed m
    refine ⟨h2, ?_⟩
    rw [show m + 1 + 2 = (m + 1) + 2 from rfl, A_rec (m + 1), h1]
    simp only [muC, H_succ]
    push_cast
    have a1 : ((m:ℝ) + 1) ≠ 0 := by positivity
    have a2 : ((m:ℝ) + 2) ≠ 0 := by positivity
    have a3 : ((m:ℝ) + 3) ≠ 0 := by positivity
    have a4 : ((m:ℝ) + 4) ≠ 0 := by positivity
    have a2' : ((m:ℝ) + 1 + 1) ≠ 0 := by positivity
    have a3' : ((m:ℝ) + 1 + 1 + 1) ≠ 0 := by positivity
    have a4' : ((m:ℝ) + 1 + 1 + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem B_closed : ∀ m : ℕ, B (m + 1) = 2 * Real.log 2 - muC (m + 1) ∧
    B (m + 2) = 2 * Real.log 2 - muC (m + 2)
  | 0 => by
    refine ⟨?_, ?_⟩
    · rw [B_one]; simp [muC]; ring
    · rw [B_rec 0, B_zero]; simp [muC]; ring
  | m + 1 => by
    obtain ⟨h1, h2⟩ := B_closed m
    refine ⟨h2, ?_⟩
    rw [show m + 1 + 2 = (m + 1) + 2 from rfl, B_rec (m + 1), h1]
    simp only [muC]
    push_cast
    have a1 : ((m:ℝ) + 1) ≠ 0 := by positivity
    have a2 : ((m:ℝ) + 2) ≠ 0 := by positivity
    have a3 : ((m:ℝ) + 3) ≠ 0 := by positivity
    have a4 : ((m:ℝ) + 4) ≠ 0 := by positivity
    have a2' : ((m:ℝ) + 1 + 1) ≠ 0 := by positivity
    have a3' : ((m:ℝ) + 1 + 1 + 1) ≠ 0 := by positivity
    have a4' : ((m:ℝ) + 1 + 1 + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma d_neg (n : ℕ) (x : ℝ) : d n (-x) = (-1) ^ (n + 1) * d n x := by
  have h1 : HasDerivAt (fun y => p n (-y)) (d n (-x) * (-1)) x :=
    (hasDerivAt_p n (-x)).comp x (hasDerivAt_neg x)
  have e : (fun y => p n (-y)) = fun y => (-1) ^ n * p n y := funext (p_neg n)
  rw [e] at h1
  have h2 : HasDerivAt (fun y => (-1) ^ n * p n y) ((-1) ^ n * d n x) x := (hasDerivAt_p n x).const_mul _
  have := h1.unique h2
  rw [pow_succ]
  linarith

lemma C_eq (m : ℕ) : C m = (-1) ^ m * B m := by
  unfold C B
  rw [← integral_const_mul]
  have e : ∀ x : ℝ, Real.log (1 - x) * ((x - 1) * d m x) =
      (fun y => (-1) ^ m * (Real.log (1 + y) * ((y + 1) * d m y))) (-x) := by
    intro x
    simp only [d_neg, ← sub_eq_add_neg]
    rw [show -x + 1 = 1 - x by ring, pow_succ]
    have : ((-1:ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    linear_combination (Real.log (1 - x) * (x - 1) * d m x) * (-this)
  simp only [e]
  have h := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 1)
    (fun y => (-1:ℝ) ^ m * (Real.log (1 + y) * ((y + 1) * d m y)))
  simp only [neg_neg] at h
  exact h

theorem nu_closed (n : ℕ) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) ^ 2 * p (n + 1) x =
      muC (n + 1) * (2 * Real.log 2 - 2 * H n - 2 * H (n + 2)) := by
  rw [RHNu0514.nu_succ]
  have hA := (A_closed n).1
  unfold A at hA
  rw [hA]
  simp only [muC]
  have a1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  have a2 : ((n:ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem kappa_closed (n : ℕ) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) * Real.log (1 - x) * p (n + 1) x =
      -(((-1) ^ (n + 1) + 1) * (2 * Real.log 2 - muC (n + 1))) / (((n:ℝ) + 1) * ((n:ℝ) + 2)) := by
  rw [RHKappa0514.kappa_succ]
  have hC := C_eq (n + 1)
  have hB := (B_closed n).1
  unfold C at hC
  unfold B at hB hC
  rw [hC, hB]
  ring

end RHNuK0514

