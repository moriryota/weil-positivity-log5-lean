import GForm0505
import BallVec0504

/-! # 0505: ball algorithm enclosing the Legendre vector `γ n J r`

Coefficients `rq : List (ℤ × ℕ)` (numerator, positive denominator); `r j = num_j/den_j`.
State `(a, b, acc)`: `a ⊇ α n j`, `b ⊇ β n j`, `acc ⊇ Σ_{i<j}` terms of `γ`.
`VecMem S (γ n J r) (run S n rq J).2.2`. -/

open Finset
open scoped BigOperators

namespace RHAlgoBall0505
open RHBall0504 RHBallVec0504 RHSparse0504 RHIter0505 RHGForm0505

def vneg (bs : List Ball) : List Ball := mapI (fun _ b => neg b) 0 bs

lemma vecMem_vneg {S : ℕ} (hS : 0 < S) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs) :
    VecMem S (fun l => -c l) (vneg bs) :=
  vecMem_mapI hS _ h (fun l hm => mem_neg hm) (fun l hl => by simp [hl])

/-- `b + (−1)^n refl b`. -/
def sym (n : ℕ) (bs : List Ball) : List Ball :=
  vadd bs (if n % 2 = 0 then vrefl bs else vneg (vrefl bs))

lemma vecMem_sym {S : ℕ} (hS : 0 < S) (n : ℕ) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs) :
    VecMem S (fun l => c l + (-1) ^ n * refl c l) (sym n bs) := by
  unfold sym
  have hr := vecMem_vrefl hS h
  split_ifs with hn
  · have e : (fun l => c l + (-1) ^ n * refl c l) = fun l => c l + (-1) ^ l * c l := by
      funext l; rw [(Nat.even_iff.mpr hn).neg_one_pow]; simp [RHGForm0505.refl]
    rw [e]; exact vecMem_vadd h hr
  · have ho : Odd n := Nat.odd_iff.mpr (by omega)
    have e : (fun l => c l + (-1) ^ n * refl c l) = fun l => c l + -((-1) ^ l * c l) := by
      funext l; rw [ho.neg_one_pow]; simp [RHGForm0505.refl]
    rw [e]; exact vecMem_vadd h (vecMem_vneg hS hr)

def rnum (rq : List (ℤ × ℕ)) (j : ℕ) : ℤ := (rq.getD j (0, 1)).1
def rden (rq : List (ℤ × ℕ)) (j : ℕ) : ℕ := (rq.getD j (0, 1)).2
noncomputable def rval (rq : List (ℤ × ℕ)) (j : ℕ) : ℝ := (rnum rq j : ℝ) / (rden rq j : ℝ)

def term (n : ℕ) (rq : List (ℤ × ℕ)) (j : ℕ) (a b : List Ball) : List Ball :=
  vsub (vsmul (rnum rq j) (rden rq j * (j + 1)) (sym n b))
    (vsmul (rnum rq j * (j.factorial : ℤ)) (rden rq j) (sym n a))

def run (S n : ℕ) (rq : List (ℤ × ℕ)) : ℕ → List Ball × List Ball × List Ball
  | 0 => (vunit S n, vunit S n, [])
  | j + 1 =>
      let st := run S n rq j
      let a := vIm st.1
      let b := vadd st.2.1 (vX st.2.1)
      (a, b, vadd st.2.2 (term n rq j a b))

theorem run_mem {S : ℕ} (hS : 0 < S) (n : ℕ) (rq : List (ℤ × ℕ)) (hden : ∀ j, 0 < rden rq j) :
    ∀ J, VecMem S (α n J) (run S n rq J).1 ∧ VecMem S (β n J) (run S n rq J).2.1 ∧
      VecMem S (γ n J (rval rq)) (run S n rq J).2.2
  | 0 => by
      refine ⟨vecMem_vunit hS n, vecMem_vunit hS n, ?_⟩
      intro l
      show mem S (γ n 0 (rval rq) l) (gz [] l)
      simp [γ, mem]
  | J + 1 => by
      obtain ⟨ha, hb, hc⟩ := run_mem hS n rq hden J
      have ha' : VecMem S (α n (J + 1)) (vIm (run S n rq J).1) := vecMem_vIm hS ha
      have hb' : VecMem S (β n (J + 1)) (vadd (run S n rq J).2.1 (vX (run S n rq J).2.1)) :=
        vecMem_vadd hb (vecMem_vX hS hb)
      refine ⟨ha', hb', ?_⟩
      have hd := hden J
      have t1 := vecMem_vsmul hS (rnum rq J) (d := rden rq J * (J + 1)) (by positivity) (vecMem_sym hS n hb')
      have t2 := vecMem_vsmul hS (rnum rq J * (J.factorial : ℤ)) (d := rden rq J) hd (vecMem_sym hS n ha')
      have t := vecMem_vadd hc (vecMem_vsub t1 t2)
      have e : (γ n (J + 1) (rval rq)) = fun l => γ n J (rval rq) l +
          ((β n (J + 1) l + (-1) ^ n * refl (β n (J + 1)) l) * (rnum rq J : ℝ) / ((rden rq J * (J + 1) : ℕ) : ℝ) -
            (α n (J + 1) l + (-1) ^ n * refl (α n (J + 1)) l) * ((rnum rq J * (J.factorial : ℤ) : ℤ) : ℝ) /
              ((rden rq J : ℕ) : ℝ)) := by
        funext l
        unfold γ
        rw [sum_range_succ]
        congr 1
        unfold rval
        have : (0 : ℝ) < rden rq J := by exact_mod_cast hd
        push_cast
        field_simp
      rw [e]
      exact t

end RHAlgoBall0505

