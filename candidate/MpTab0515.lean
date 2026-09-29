import MpTabData0515

/-! # 0515: soundness of the `M⁺` table: row `j` encloses `∫ log(1+x) P_j P_l` for every valid `l`.
 -/

namespace RHMpTab0515
open RHBall0504 RHBallVec0504 RHRec2D0515 RHTabCore0515 RHLeg0503 RHBallMisc0512

lemma Mw0 (i : ℕ) : Mw (fun x => Real.log (1 + x)) 0 i = RHNuK0514.muC i := by
  unfold Mw; simp only [p_zero, one_mul]; exact RHNuK0514.mu_eq i

lemma mem_mu0 : mem (2 ^ 256) (RHNuK0514.muC 0) mu0B := by
  obtain ⟨h1, h2⟩ := Trial0455.log2_bounds
  have q1 : ((mu0B.1 : ℚ) - mu0B.2) / (2 ^ 256 : ℕ) ≤ 2 * Trial0455.lo - 2 := by decide +kernel
  have q2 : 2 * Trial0455.hi - 2 ≤ ((mu0B.1 : ℚ) + mu0B.2) / (2 ^ 256 : ℕ) := by decide +kernel
  have r1 : ((((mu0B.1 : ℚ) - mu0B.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) ≤ ((2 * Trial0455.lo - 2 : ℚ) : ℝ) := by
    exact_mod_cast q1
  have r2 : ((2 * Trial0455.hi - 2 : ℚ) : ℝ) ≤ ((((mu0B.1 : ℚ) + mu0B.2) / (2 ^ 256 : ℕ) : ℚ) : ℝ) := by
    exact_mod_cast q2
  simp only [mu0B] at r1 r2 ⊢
  push_cast at r1 r2
  apply mem_of_bounds' (by positivity)
  · simp only [RHNuK0514.muC]; push_cast; linarith
  · simp only [RHNuK0514.muC]; push_cast; linarith

lemma mem_muB (l : ℕ) : mem (2 ^ 256) (RHNuK0514.muC l) (muB l) := by
  cases l with
  | zero => simpa [muB] using mem_mu0
  | succ n =>
    have hD : 0 < (n + 1) * (n + 1 + 1) := by positivity
    have h := mem_ratBall (S := 2 ^ 256) (by positivity) (if (n + 1) % 2 = 1 then 2 else -2) hD
    simp only [muB, if_neg (Nat.succ_ne_zero n)]
    convert h using 1
    simp only [RHNuK0514.muC]
    rcases Nat.even_or_odd n with he | ho
    · have : (n + 1) % 2 = 1 := by rcases he with ⟨k, hk⟩; omega
      rw [if_pos this, pow_add, he.neg_one_pow]; push_cast; ring
    · have : ¬ (n + 1) % 2 = 1 := by rcases ho with ⟨k, hk⟩; omega
      rw [if_neg this, pow_add, ho.neg_one_pow]; push_cast; ring

lemma base_row : RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x)) 0) (tab.getD 0 []) := by
  rw [tab_base]
  intro i hi
  simp only [base, List.length_map, List.length_range] at hi
  have e : gz base i = muB i := by
    simp [gz, base, List.getD_eq_getElem?_getD, hi]
  rw [e, Mw0]
  exact mem_muB i

theorem Mp_mem : ∀ j, RowMem (2 ^ 256) (Mw (fun x => Real.log (1 + x)) j) (tab.getD j []) :=
  rows_mem (by positivity) _ RHLogMoment0508.log1p_ii tab tab_chk1 tab_chk base_row

end RHMpTab0515

