import EulerRemainder0463

/-! # 0495 T4 pilot, step 3a: Euler–Maclaurin enclosure of `S1 = ∑ 1/(4m+1)^2`

Mirrors 0461–0463 (γ) with `f x = (4x+1)^(-2)`. For `N ≥ 1`:
`|S1 - C N s| ≤ sawBound (s+1) * (s+1)! * 4^s * (4N+1)^(-(s+2))`. -/

open Set intervalIntegral Filter
open scoped Topology

namespace RHHurwitzEM0495

noncomputable def f (x : ℝ) : ℝ := ((4:ℝ) * x + 1) ^ (-2 : ℤ)

noncomputable def fd (k : ℕ) (x : ℝ) : ℝ :=
  (-4:ℝ) ^ k * ((k + 1).factorial : ℝ) * ((4:ℝ) * x + 1) ^ (-2 - (k : ℤ))

lemma fd_zero : fd 0 = f := by funext x; simp [fd, f]

lemma fd_hasDerivAt (k : ℕ) {x : ℝ} (hx : 0 < 4 * x + 1) :
    HasDerivAt (fd k) (fd (k + 1) x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 4 * y + 1) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul (4:ℝ)).add_const (1:ℝ)
  have h := ((hasDerivAt_zpow (-2 - (k : ℤ)) (4 * x + 1) (Or.inl hx.ne')).comp x hlin).const_mul
    ((-4:ℝ) ^ k * ((k + 1).factorial : ℝ))
  unfold fd
  convert h using 1
  · rfl
  · have he : (-2 - ((k + 1 : ℕ) : ℤ)) = (-2 - (k : ℤ)) - 1 := by push_cast; ring
    rw [he, Nat.factorial_succ (k + 1)]
    push_cast
    ring

lemma iter_eq (k : ℕ) : EqOn (iteratedDerivWithin k f (Ioi 0)) (fd k) (Ioi 0) := by
  induction k with
  | zero => intro x _; simp [fd_zero]
  | succ k ih =>
    intro x hx
    have hx' : (0:ℝ) < 4 * x + 1 := by have : (0:ℝ) < x := hx; linarith
    have hd : HasDerivAt (iteratedDerivWithin k f (Ioi 0)) (fd (k + 1) x) x :=
      (fd_hasDerivAt k hx').congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) ih)
    rw [iteratedDerivWithin_succ, hd.hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffWithinAt hx)]

lemma f_eq : f = fun x : ℝ => ((4 * x + 1) ^ 2)⁻¹ := by
  funext x; simp [f, zpow_neg]

lemma f_smooth (k : ℕ) : ContDiffOn ℝ k f (Ioi 0) := by
  rw [f_eq]
  apply ContDiffOn.inv
  · exact (((contDiff_const.mul contDiff_id).add contDiff_const).pow 2).contDiffOn
  · intro x hx; have : (0:ℝ) < x := hx; positivity

/-- Partial sums of `S1`. -/
noncomputable def P (n : ℕ) : ℝ := ∑ m ∈ Finset.range n, f m

lemma P_succ (k : ℕ) : P (k + 1) = P k + f k := by unfold P; rw [Finset.sum_range_succ]

lemma trapezoid_f (N n : ℕ) :
    trapezoid_sum f N n = P (N + n) - P N - f N / 2 + f (N + n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [trapezoid_sum_succ, ih, show N + (n + 1) = (N + n) + 1 from rfl, P_succ]
    push_cast
    ring

noncomputable def Iinf (y : ℝ) : ℝ := 1 / (4 * (4 * y + 1))

lemma integral_f (N n : ℕ) (hN : 0 < N) : (∫ x in (N : ℝ)..N + n, f x) = Iinf N - Iinf (N + n) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hle : (N:ℝ) ≤ N + n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hd : ∀ x ∈ uIcc (N : ℝ) (N + n), HasDerivAt (fun y => -Iinf y) (f x) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have hx' : (0:ℝ) < 4 * x + 1 := by linarith [hx.1]
    have hlin : HasDerivAt (fun y : ℝ => 4 * (4 * y + 1)) (4 * 4) x := by
      simpa using (((hasDerivAt_id x).const_mul (4:ℝ)).add_const (1:ℝ)).const_mul (4:ℝ)
    have h := (hlin.inv (by positivity)).neg
    unfold Iinf f
    convert h using 1
    · funext y; simp [one_div]
    · rw [zpow_neg, zpow_two]; field_simp
  have hint : IntervalIntegrable f MeasureTheory.volume (N : ℝ) (N + n) := by
    apply ContinuousOn.intervalIntegrable
    apply (f_smooth 0).continuousOn.mono
    intro x hx
    rw [uIcc_of_le hle] at hx
    show (0:ℝ) < x
    linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring


noncomputable def cj (j : ℕ) : ℝ := (-1 : ℝ) ^ j * saw (j + 2) 0

noncomputable def bc (s : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range s, cj j * fd (j + 1) y

/-- Corrected approximation of `S1` from the first `N` terms. -/
noncomputable def C (N s : ℕ) : ℝ := P N + f N / 2 + Iinf N - bc s N

theorem em_f (N n s : ℕ) (hN : 0 < N) :
    P (N + n) - P N - f N / 2 + f (N + n) / 2 =
      (Iinf N - Iinf (N + n)) + (bc s (N + n) - bc s N) +
      (-1 : ℝ) ^ s * ∫ x in (N : ℝ)..N + n, saw (s + 1) x * fd (s + 1) x := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hle : (N:ℝ) ≤ N + n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hb : Icc ((N : ℤ) : ℝ) ((N : ℤ) + n) ⊆ Ioi (0 : ℝ) := by
    intro x hx; simp only [Int.cast_natCast] at hx; exact lt_of_lt_of_le hNr hx.1
  have h := trapezoid_sum_eq_integral_add (a := (N : ℤ)) (n := n) (f_smooth (s + 1))
    (uniqueDiffOn_Ioi 0) hb
  simp only [Int.cast_natCast, smul_eq_mul] at h
  rw [trapezoid_f, integral_f N n hN] at h
  have hM : (0:ℝ) < N + n := by linarith
  have hi : (∫ x in (N : ℝ)..N + n, saw (s + 1) x * iteratedDerivWithin (s + 1) f (Ioi 0) x) =
      ∫ x in (N : ℝ)..N + n, saw (s + 1) x * fd (s + 1) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hle] at hx
    simp only [iter_eq (s + 1) (show x ∈ Ioi (0:ℝ) from lt_of_lt_of_le hNr hx.1)]
  rw [hi] at h
  have hs : ∀ y : ℝ, 0 < y → ∑ j ∈ Finset.range s, (-1 : ℝ) ^ j * (saw (j + 2) 0 *
      (iteratedDerivWithin (j + 1) f (Ioi 0) (N + n) - iteratedDerivWithin (j + 1) f (Ioi 0) N)) =
      bc s (N + n) - bc s N := by
    intro _ _
    unfold bc cj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [iter_eq (j + 1) (show (N:ℝ) + n ∈ Ioi 0 from hM), iter_eq (j + 1) (show (N:ℝ) ∈ Ioi 0 from hNr)]
    ring
  rw [hs 1 one_pos] at h
  linarith

lemma fd_abs (k : ℕ) {x : ℝ} (hx : 0 < 4 * x + 1) :
    |fd k x| = (4:ℝ) ^ k * ((k + 1).factorial : ℝ) * (4 * x + 1) ^ (-2 - (k : ℤ)) := by
  unfold fd
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k+1).factorial : ℝ)),
    abs_of_pos (zpow_pos hx _)]
  norm_num

lemma zpow_integral (N n : ℕ) (hN : 0 < N) (k : ℕ) :
    (∫ x in (N : ℝ)..N + n, ((4:ℝ) * x + 1) ^ (-2 - ((k + 1 : ℕ) : ℤ))) ≤
      ((4:ℝ) * N + 1) ^ (-((k + 2 : ℕ) : ℤ)) / (4 * (k + 2)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hle : (N:ℝ) ≤ N + n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set m : ℤ := -((k + 2 : ℕ) : ℤ) with hm
  have hk : (m : ℝ) ≠ 0 := by rw [hm]; push_cast; linarith
  have hd : ∀ x ∈ uIcc (N : ℝ) (N + n),
      HasDerivAt (fun y => ((4:ℝ) * y + 1) ^ m / (4 * m)) (((4:ℝ) * x + 1) ^ (-2 - ((k + 1 : ℕ) : ℤ))) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have hx' : (0:ℝ) < 4 * x + 1 := by linarith [hx.1]
    have hlin : HasDerivAt (fun y : ℝ => 4 * y + 1) 4 x := by
      simpa using ((hasDerivAt_id x).const_mul (4:ℝ)).add_const (1:ℝ)
    have h := ((hasDerivAt_zpow m (4 * x + 1) (Or.inl hx'.ne')).comp x hlin).div_const (4 * (m:ℝ))
    convert h using 1
    · rfl
    · have he : (-2 - ((k + 1 : ℕ) : ℤ)) = m - 1 := by rw [hm]; push_cast; ring
      rw [he]
      field_simp
  have hint : IntervalIntegrable (fun x : ℝ => ((4:ℝ) * x + 1) ^ (-2 - ((k + 1 : ℕ) : ℤ)))
      MeasureTheory.volume (N : ℝ) (N + n) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hle] at hx
    have hx' : (0:ℝ) < 4 * x + 1 := by linarith [hx.1]
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.zpow₀ _
      (Or.inl hx'.ne') |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hmr : (m : ℝ) = -((k:ℝ) + 2) := by rw [hm]; push_cast; ring
  have hpos : 0 ≤ ((4:ℝ) * (N + n) + 1) ^ m := (zpow_pos (by positivity) _).le
  have hk2 : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hk2' : (k:ℝ) + 2 ≠ 0 := hk2.ne'
  rw [hmr, div_sub_div_same,
    show ∀ a b : ℝ, (a - b) / (4 * -((k:ℝ) + 2)) = (b - a) / (4 * ((k:ℝ) + 2)) from
      fun a b => by field_simp; ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [hpos]

theorem remainder_bound (N n s : ℕ) (hN : 0 < N) :
    |∫ x in (N : ℝ)..N + n, saw (s + 1) x * fd (s + 1) x| ≤
      sawBound (s + 1) * ((s + 1).factorial : ℝ) * 4 ^ s * ((4:ℝ) * N + 1) ^ (-((s + 2 : ℕ) : ℤ)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hle : (N:ℝ) ≤ N + n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hK : 0 ≤ sawBound (s + 1) * ((4:ℝ) ^ (s + 1) * ((s + 1 + 1).factorial : ℝ)) :=
    mul_nonneg sawBound_nonneg (by positivity)
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := fun x => saw (s + 1) x * fd (s + 1) x)
    (g := fun x => sawBound (s + 1) * ((4:ℝ) ^ (s + 1) * ((s + 1 + 1).factorial : ℝ) *
      ((4:ℝ) * x + 1) ^ (-2 - ((s + 1 : ℕ) : ℤ)))) hle
    (Filter.Eventually.of_forall (fun x hx => by
      have hx' : (0:ℝ) < 4 * x + 1 := by linarith [hx.1]
      rw [Real.norm_eq_abs, abs_mul, fd_abs (s + 1) hx']
      exact mul_le_mul (abs_saw_le _ _) le_rfl (by positivity) sawBound_nonneg))
    (by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le hle] at hx
      have hx' : (0:ℝ) < 4 * x + 1 := by linarith [hx.1]
      have hc : ContinuousAt (fun y : ℝ => ((4:ℝ) * y + 1) ^ (-2 - ((s + 1 : ℕ) : ℤ))) x :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.zpow₀ _ (Or.inl hx'.ne')
      exact ((continuousAt_const (y := sawBound (s + 1) * ((4:ℝ) ^ (s + 1) * ((s + 1 + 1).factorial : ℝ)))).mul
        hc).continuousWithinAt.congr (fun y _ => by simp only [Pi.mul_apply]; ring) (by simp only [Pi.mul_apply]; ring))
  rw [Real.norm_eq_abs] at hb
  refine hb.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hz := zpow_integral N n hN s
  have hfac : ((s + 1 + 1).factorial : ℝ) = ((s + 2 : ℕ) : ℝ) * ((s + 1).factorial : ℝ) := by
    rw [show s + 1 + 1 = (s + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  have hs2 : (0:ℝ) < ((s + 2 : ℕ) : ℝ) := by positivity
  calc sawBound (s + 1) * ((4:ℝ) ^ (s + 1) * (((s + 2 : ℕ) : ℝ) * ((s + 1).factorial : ℝ)) *
        ∫ x in (N : ℝ)..N + n, ((4:ℝ) * x + 1) ^ (-2 - ((s + 1 : ℕ) : ℤ)))
      ≤ sawBound (s + 1) * ((4:ℝ) ^ (s + 1) * (((s + 2 : ℕ) : ℝ) * ((s + 1).factorial : ℝ)) *
        (((4:ℝ) * N + 1) ^ (-((s + 2 : ℕ) : ℤ)) / (4 * ((s:ℝ) + 2)))) := by
          apply mul_le_mul_of_nonneg_left _ sawBound_nonneg
          exact mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by push_cast; field_simp; ring


lemma f_nonneg (x : ℝ) : 0 ≤ f x := by rw [f_eq]; positivity

lemma f_summable : Summable (fun m : ℕ => f m) := by
  have hb : Summable (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  refine hb.of_nonneg_of_le (fun m => f_nonneg m) (fun m => ?_)
  rw [f_eq]
  push_cast
  rw [one_div]
  apply inv_anti₀ (by positivity)
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

noncomputable def S1 : ℝ := ∑' m : ℕ, f m

noncomputable def tailT (s : ℕ) (y : ℝ) : ℝ := f y / 2 + Iinf y - bc s y

lemma lin_tendsto (N : ℕ) : Tendsto (fun n : ℕ => (4:ℝ) * ((N:ℝ) + n) + 1) atTop atTop := by
  apply tendsto_atTop_add_const_right
  apply Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 4)
  exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop

lemma zpow_tendsto (N : ℕ) {m : ℤ} (hm : m < 0) :
    Tendsto (fun n : ℕ => ((4:ℝ) * ((N:ℝ) + n) + 1) ^ m) atTop (𝓝 0) :=
  (tendsto_zpow_atTop_zero hm).comp (lin_tendsto N)

lemma tailT_tendsto (N s : ℕ) : Tendsto (fun n : ℕ => tailT s ((N:ℝ) + n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => f ((N:ℝ) + n) / 2) atTop (𝓝 0) := by
    simpa [f] using (zpow_tendsto N (m := -2) (by norm_num)).div_const 2
  have h2 : Tendsto (fun n : ℕ => Iinf ((N:ℝ) + n)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp ((lin_tendsto N).const_mul_atTop (by norm_num : (0:ℝ) < 4)))
    refine this.congr (fun n => ?_)
    simp [Iinf, Function.comp, one_div]
  have h3 : Tendsto (fun n : ℕ => bc s ((N:ℝ) + n)) atTop (𝓝 0) := by
    unfold bc
    rw [show (0:ℝ) = ∑ j ∈ Finset.range s, cj j * 0 by simp]
    apply tendsto_finset_sum
    intro j _
    apply Tendsto.const_mul
    unfold fd
    rw [show (0:ℝ) = (-4:ℝ) ^ (j + 1) * ((j + 1 + 1).factorial : ℝ) * 0 by ring]
    exact (zpow_tendsto N (m := -2 - ((j + 1 : ℕ) : ℤ)) (by omega)).const_mul _
  have := (h1.add h2).sub h3
  simp only [add_zero, sub_zero] at this
  exact this.congr (fun n => by simp [tailT])

noncomputable def Rb (N s : ℕ) : ℝ :=
  sawBound (s + 1) * ((s + 1).factorial : ℝ) * 4 ^ s * ((4:ℝ) * N + 1) ^ (-((s + 2 : ℕ) : ℤ))

/-- **Euler–Maclaurin enclosure of S1** (no numerical input). -/
theorem S1_bound (N s : ℕ) (hN : 0 < N) : |S1 - C N s| ≤ Rb N s := by
  have hP : Tendsto (fun n : ℕ => P (N + n)) atTop (𝓝 S1) := by
    have h := f_summable.hasSum.tendsto_sum_nat
    have h2 := h.comp (tendsto_add_atTop_nat N)
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, P, add_comm n N]
  have hlim : Tendsto (fun n : ℕ => |P (N + n) - C N s + tailT s ((N:ℝ) + n)|) atTop
      (𝓝 |S1 - C N s + 0|) :=
    ((hP.sub_const (C N s)).add (tailT_tendsto N s)).abs
  rw [add_zero] at hlim
  refine le_of_tendsto' hlim (fun n => ?_)
  have he := em_f N n s hN
  have hr := remainder_bound N n s hN
  have hid : P (N + n) - C N s + tailT s ((N:ℝ) + n) =
      (-1 : ℝ) ^ s * ∫ x in (N : ℝ)..N + n, saw (s + 1) x * fd (s + 1) x := by
    unfold C tailT
    push_cast at he ⊢
    linarith
  rw [hid, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact hr

end RHHurwitzEM0495

