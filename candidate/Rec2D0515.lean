import LogMoment0508
import BallVec0504

/-! # 0515: two-dimensional recurrence for weighted Legendre moment matrices

For an integrable weight `w` on `[-1,1]`, `Mw w j l = ∫ w P_j P_l` satisfies
`(j+1) M(j+1,l) = (2j+1)·((l+1)M(j,l+1) + l M(j,l−1))/(2l+1) − j M(j−1,l)` (natural subtraction;
the `l−1`, `j−1` terms carry the coefficient 0 when `l = 0`, `j = 0`).

Ball version: `tnext a b d l cs cm qs` (structural) computes, for each `k = l + i`,
`((l+1)/(2l+1)·c_{k+1} + k/(2k+1)·c_{k−1})·a/d − q_k·b/d`; `tnext_mem` is its enclosure lemma
on the valid prefix. -/

open Set intervalIntegral

namespace RHRec2D0515
open RHLeg0503 RHBall0504 RHBallVec0504

lemma xp (l : ℕ) (x : ℝ) :
    x * p l x = (((l:ℝ) + 1) * p (l + 1) x + (l:ℝ) * p (l - 1) x) / (2 * l + 1) := by
  cases l with
  | zero => simp [x_mul_zero]
  | succ n =>
    rw [x_mul_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

lemma pr (j : ℕ) (x : ℝ) :
    ((j:ℝ) + 1) * p (j + 1) x = (2 * j + 1) * x * p j x - j * p (j - 1) x := by
  cases j with
  | zero => simp [p_one, p_zero]
  | succ n =>
    have h := p_rec n x
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination h

noncomputable def Mw (w : ℝ → ℝ) (j l : ℕ) : ℝ := ∫ x in (-1:ℝ)..1, w x * (p j x * p l x)

theorem Mw_rec (w : ℝ → ℝ) (hw : IntervalIntegrable w MeasureTheory.volume (-1) 1) (j l : ℕ) :
    (2 * (l:ℝ) + 1) * (((j:ℝ) + 1) * Mw w (j + 1) l) =
      (2 * j + 1) * (((l:ℝ) + 1) * Mw w j (l + 1) + l * Mw w j (l - 1)) -
        (2 * (l:ℝ) + 1) * (j * Mw w (j - 1) l) := by
  have hI : ∀ a b : ℕ, IntervalIntegrable (fun x => w x * (p a x * p b x)) MeasureTheory.volume (-1) 1 :=
    fun a b => hw.mul_continuousOn ((continuous_p a).mul (continuous_p b)).continuousOn
  have hl : (2 * (l:ℝ) + 1) ≠ 0 := by positivity
  have hpt : ∀ x, (2 * (l:ℝ) + 1) * ((j:ℝ) + 1) * (w x * (p (j + 1) x * p l x)) =
      (2 * (j:ℝ) + 1) * (((l:ℝ) + 1) * (w x * (p j x * p (l + 1) x)) +
        (l:ℝ) * (w x * (p j x * p (l - 1) x))) - (2 * (l:ℝ) + 1) * (j:ℝ) * (w x * (p (j - 1) x * p l x)) := by
    intro x
    have h1 := pr j x
    have h2 := xp l x
    rw [eq_div_iff hl] at h2
    linear_combination (2 * (l:ℝ) + 1) * (w x * p l x) * h1 + ((2 * (j:ℝ) + 1) * w x * p j x) * h2
  unfold Mw
  rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
  simp only [hpt]
  rw [intervalIntegral.integral_sub (((hI j (l + 1)).const_mul _).add ((hI j (l - 1)).const_mul _) |>.const_mul _)
      ((hI (j - 1) l).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((hI j (l + 1)).const_mul _)
      ((hI j (l - 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-! ### Ball recurrence -/

def tnext (a b : ℤ) (d : ℕ) : ℕ → List Ball → Ball → List Ball → List Ball
  | l, c0 :: rest@(c1 :: _), cm, q :: qs =>
      sub (smul a d (add (smul ((l:ℤ) + 1) (2 * l + 1) c1) (smul (l:ℤ) (2 * l + 1) cm))) (smul b d q) ::
        tnext a b d (l + 1) rest c0 qs
  | _, _, _, _ => []

/-- The real value enclosed at index `k`. -/
noncomputable def tval (a b : ℤ) (d : ℕ) (c q : ℕ → ℝ) (k : ℕ) : ℝ :=
  (c (k + 1) * (((k:ℤ) + 1 : ℤ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ) + c (k - 1) * (((k:ℤ) : ℤ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) *
    (a : ℝ) / (d : ℝ) - q k * (b : ℝ) / (d : ℝ)

theorem tnext_mem {S : ℕ} (hS : 0 < S) (a b : ℤ) {d : ℕ} (hd : 0 < d) (c q : ℕ → ℝ) :
    ∀ (cs : List Ball) (l : ℕ) (cm : Ball) (qs : List Ball),
      mem S (c (l - 1)) cm → (∀ i, i < cs.length → mem S (c (l + i)) (gz cs i)) →
      (∀ i, i < qs.length → mem S (q (l + i)) (gz qs i)) →
      ∀ i, i + 1 < cs.length → i < qs.length → mem S (tval a b d c q (l + i)) (gz (tnext a b d l cs cm qs) i) := by
  intro cs
  induction cs with
  | nil => intro l cm qs _ _ _ i hi; simp at hi
  | cons c0 rest ih =>
    intro l cm qs hcm hc hq i hi hiq
    cases rest with
    | nil => simp at hi
    | cons c1 cs =>
      cases qs with
      | nil => simp at hiq
      | cons q0 qs =>
        cases i with
        | zero =>
          simp only [tnext, gz_cons_zero, Nat.add_zero]
          have h1 : mem S (c (l + 1)) c1 := by simpa using hc 1 (by simp)
          have h0 : mem S (q l) q0 := by simpa using hq 0 (by simp)
          exact mem_sub (mem_smul hS a hd (mem_add (mem_smul hS _ (by omega) h1) (mem_smul hS _ (by omega) hcm)))
            (mem_smul hS b hd h0)
        | succ i =>
          simp only [tnext, gz_cons_succ]
          have hc0 : mem S (c (l + 1 - 1)) c0 := by simpa using hc 0 (by simp)
          have hc' : ∀ i, i < (c1 :: cs).length → mem S (c (l + 1 + i)) (gz (c1 :: cs) i) := by
            intro i hi'
            have := hc (i + 1) (by simp at hi' ⊢; omega)
            rw [show l + 1 + i = l + (i + 1) by omega]
            simpa using this
          have hq' : ∀ i, i < qs.length → mem S (q (l + 1 + i)) (gz qs i) := by
            intro i hi'
            have := hq (i + 1) (by simp; omega)
            rw [show l + 1 + i = l + (i + 1) by omega]
            simpa using this
          have := ih (l + 1) c0 qs hc0 hc' hq' i (by simp at hi ⊢; omega) (by simp at hiq; omega)
          rw [show l + (i + 1) = l + 1 + i by omega]
          exact this

theorem tnext_length (a b : ℤ) (d : ℕ) :
    ∀ (cs : List Ball) (l : ℕ) (cm : Ball) (qs : List Ball),
      (tnext a b d l cs cm qs).length = min (cs.length - 1) qs.length := by
  intro cs
  induction cs with
  | nil => intro l cm qs; simp [tnext]
  | cons c0 rest ih =>
    intro l cm qs
    cases rest with
    | nil => simp [tnext]
    | cons c1 cs =>
      cases qs with
      | nil => simp [tnext]
      | cons q0 qs =>
        simp only [tnext, List.length_cons]
        rw [ih]
        simp only [List.length_cons]
        omega

/-- Validity of a row on its whole length. -/
def RowMem (S : ℕ) (f : ℕ → ℝ) (bs : List Ball) : Prop := ∀ i, i < bs.length → mem S (f i) (gz bs i)

theorem row_one {S : ℕ} (hS : 0 < S) (w : ℝ → ℝ) (hw : IntervalIntegrable w MeasureTheory.volume (-1) 1)
    {r0 : List Ball} (h0 : RowMem S (Mw w 0) r0) :
    RowMem S (Mw w 1) (tnext 1 0 1 0 r0 (gz r0 0) r0) := by
  intro i hi
  rw [tnext_length] at hi
  have hm : mem S (Mw w 0 (0 - 1)) (gz r0 0) := h0 0 (by omega)
  have h := tnext_mem hS 1 0 (d := 1) (by norm_num) (Mw w 0) (Mw w 0) r0 0 (gz r0 0) r0 hm
    (fun i hi => by simpa using h0 i hi) (fun i hi => by simpa using h0 i hi) i (by omega) (by omega)
  have e : tval 1 0 1 (Mw w 0) (Mw w 0) (0 + i) = Mw w 1 i := by
    have r := Mw_rec w hw 0 i
    have hl : (2 * (i:ℝ) + 1) ≠ 0 := by positivity
    have hM : Mw w 1 i = (((i:ℝ) + 1) * Mw w 0 (i + 1) + i * Mw w 0 (i - 1)) / (2 * i + 1) := by
      rw [eq_div_iff hl]; push_cast at r; linarith
    rw [hM]
    simp only [tval, Nat.zero_add]
    push_cast
    field_simp
    ring
  rw [e] at h
  exact h

theorem row_step {S : ℕ} (hS : 0 < S) (w : ℝ → ℝ) (hw : IntervalIntegrable w MeasureTheory.volume (-1) 1)
    (j : ℕ) {r1 r0 : List Ball} (h1 : RowMem S (Mw w (j + 1)) r1) (h0 : RowMem S (Mw w j) r0) :
    RowMem S (Mw w (j + 2)) (tnext (2 * (j:ℤ) + 3) ((j:ℤ) + 1) (j + 2) 0 r1 (gz r1 0) r0) := by
  intro i hi
  rw [tnext_length] at hi
  have hm : mem S (Mw w (j + 1) (0 - 1)) (gz r1 0) := h1 0 (by omega)
  have h := tnext_mem hS (2 * (j:ℤ) + 3) ((j:ℤ) + 1) (d := j + 2) (by omega) (Mw w (j + 1)) (Mw w j) r1 0 (gz r1 0) r0 hm
    (fun i hi => by simpa using h1 i hi) (fun i hi => by simpa using h0 i hi) i (by omega) (by omega)
  have e : tval (2 * (j:ℤ) + 3) ((j:ℤ) + 1) (j + 2) (Mw w (j + 1)) (Mw w j) (0 + i) = Mw w (j + 2) i := by
    have r := Mw_rec w hw (j + 1) i
    have hl : (2 * (i:ℝ) + 1) ≠ 0 := by positivity
    have hj : ((j:ℝ) + 2) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel] at r
    push_cast at r
    have hM : Mw w (j + 2) i = ((2 * (j:ℝ) + 3) * (((i:ℝ) + 1) * Mw w (j + 1) (i + 1) + i * Mw w (j + 1) (i - 1)) -
        (2 * (i:ℝ) + 1) * (((j:ℝ) + 1) * Mw w j i)) / ((2 * i + 1) * ((j:ℝ) + 2)) := by
      rw [eq_div_iff (mul_ne_zero hl hj)]; linear_combination r
    rw [hM]
    simp only [tval, Nat.zero_add]
    push_cast
    field_simp
  rw [e] at h
  exact h

end RHRec2D0515

