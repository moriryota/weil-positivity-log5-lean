import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # 0500: list polynomials with rational coefficients

Kernel-computable polynomial arithmetic on `List ℚ` (coefficients in increasing degree) with
evaluation lemmas over `ℝ`, and the coefficient-absolute-value bound on `[0, a]`.
Used to certify truncation bounds by `decide +kernel`. -/

open Finset
open scoped BigOperators

namespace RHPolyL0500

/-- Evaluation over `ℝ` (Horner). -/
noncomputable def ev : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, t => (c : ℝ) + t * ev p t

/-- Evaluation over `ℚ` (Horner). -/
def evQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, t => c + t * evQ p t

def addL : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

def smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => c * a :: smul c p

def mulL : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: p, q => addL (smul c q) (0 :: mulL p q)

def subL (p q : List ℚ) : List ℚ := addL p (smul (-1) q)

def absL : List ℚ → List ℚ
  | [] => []
  | a :: p => |a| :: absL p

lemma ev_addL : ∀ (p q : List ℚ) (t : ℝ), ev (addL p q) t = ev p t + ev q t
  | [], q, t => by simp [addL, ev]
  | a :: p, [], t => by simp [addL, ev]
  | a :: p, b :: q, t => by
      simp only [addL, ev, ev_addL p q t]; push_cast; ring

lemma ev_smul (c : ℚ) : ∀ (p : List ℚ) (t : ℝ), ev (smul c p) t = c * ev p t
  | [], t => by simp [smul, ev]
  | a :: p, t => by simp only [smul, ev, ev_smul c p t]; push_cast; ring

lemma ev_mulL : ∀ (p q : List ℚ) (t : ℝ), ev (mulL p q) t = ev p t * ev q t
  | [], q, t => by simp [mulL, ev]
  | c :: p, q, t => by
      rw [mulL, ev_addL, ev_smul, ev, ev, ev_mulL p q t]; push_cast; ring

lemma ev_subL (p q : List ℚ) (t : ℝ) : ev (subL p q) t = ev p t - ev q t := by
  rw [subL, ev_addL, ev_smul]; push_cast; ring

lemma ev_cast : ∀ (p : List ℚ) (a : ℚ), ev p (a : ℝ) = ((evQ p a : ℚ) : ℝ)
  | [], a => by simp [ev, evQ]
  | c :: p, a => by simp only [ev, evQ, ev_cast p a]; push_cast; ring

lemma ev_absL_nonneg : ∀ (p : List ℚ) {t : ℝ}, 0 ≤ t → 0 ≤ ev (absL p) t
  | [], t, _ => by simp [absL, ev]
  | c :: p, t, ht => by
      simp only [absL, ev]
      have := ev_absL_nonneg p ht
      have hc : (0:ℝ) ≤ ((|c| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg c
      positivity

lemma abs_ev_le : ∀ (p : List ℚ) {t : ℝ}, 0 ≤ t → |ev p t| ≤ ev (absL p) t
  | [], t, _ => by simp [absL, ev]
  | c :: p, t, ht => by
      simp only [absL, ev]
      have ih := abs_ev_le p ht
      have hc : |(c : ℝ)| = ((|c| : ℚ) : ℝ) := by push_cast; rfl
      calc |(c : ℝ) + t * ev p t| ≤ |(c : ℝ)| + |t * ev p t| := abs_add_le _ _
        _ = ((|c| : ℚ) : ℝ) + t * |ev p t| := by rw [hc, abs_mul, abs_of_nonneg ht]
        _ ≤ ((|c| : ℚ) : ℝ) + t * ev (absL p) t := by gcongr

lemma ev_absL_mono : ∀ (p : List ℚ) {t a : ℝ}, 0 ≤ t → t ≤ a → ev (absL p) t ≤ ev (absL p) a
  | [], t, a, _, _ => by simp [absL, ev]
  | c :: p, t, a, ht, hta => by
      simp only [absL, ev]
      have ih := ev_absL_mono p ht hta
      have h0 := ev_absL_nonneg p ht
      have : t * ev (absL p) t ≤ a * ev (absL p) a :=
        mul_le_mul hta ih h0 (ht.trans hta)
      linarith

/-- `|p(t)| ≤ ∑ |p_j| a^j` for `0 ≤ t ≤ a`, as a rational number. -/
lemma abs_ev_le_evQ (p : List ℚ) {t : ℝ} (a : ℚ) (ht : 0 ≤ t) (hta : t ≤ a) :
    |ev p t| ≤ ((evQ (absL p) a : ℚ) : ℝ) := by
  rw [← ev_cast]
  exact (abs_ev_le p ht).trans (ev_absL_mono p ht hta)

lemma ev_append : ∀ (p q : List ℚ) (t : ℝ), ev (p ++ q) t = ev p t + t ^ p.length * ev q t
  | [], q, t => by simp [ev]
  | c :: p, q, t => by
      simp only [List.cons_append, ev, ev_append p q t, List.length_cons]; ring

lemma ev_range (f : ℕ → ℚ) (t : ℝ) :
    ∀ n : ℕ, ev ((List.range n).map f) t = ∑ i ∈ range n, (f i : ℝ) * t ^ i
  | 0 => by simp [ev]
  | n + 1 => by
      rw [List.range_succ, List.map_append, ev_append, ev_range f t n, Finset.sum_range_succ]
      simp [ev]; ring

lemma ev_drop_two {p : List ℚ} (h : p.take 2 = [0, 0]) (t : ℝ) :
    ev p t = t ^ 2 * ev (p.drop 2) t := by
  conv_lhs => rw [← List.take_append_drop 2 p, h]
  simp [ev]; ring

end RHPolyL0500
