import ResidualTraceBound
import ComparisonEnergy
import WeilColumnCandidate
import ParitySplit

open MeasureTheory Set
open scoped BigOperators Matrix
namespace RHConditionalLog5
noncomputable section
open RHTargetFormBinding RHLog5Bridge RHResidualCertificate RHCertificateData

abbrev H := Lp ℝ 2 (volume : Measure ℝ)
abbrev I := Fin 32
noncomputable def embed (u : ℝ → ℝ) : H := by
  classical
  exact if h : MemLp u 2 volume then h.toLp u else 0
noncomputable def recPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C (1 / halfWidth) * Polynomial.X
  | n+2 => (Polynomial.X * recPoly (n+1) * Polynomial.C ((2*(n:ℝ)+3)/halfWidth) -
      recPoly n * Polynomial.C ((n:ℝ)+1)) * Polynomial.C (1/((n:ℝ)+2))
noncomputable def basisPoly (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (Real.sqrt ((2*(n:ℝ)+1)/(2*halfWidth))) * recPoly n
noncomputable def basis (n : ℕ) : ℝ → ℝ :=
  RHWeilColumnCandidate.zeroPoly halfWidth (basisPoly n)
def degree (o : Bool) (n : ℕ) : ℕ := 2*n + if o then 1 else 0
noncomputable def component (o : Bool) (u : ℝ → ℝ) : ℝ → ℝ :=
  if o then fun x => (u x-u (-x))/2 else fun x => (u x+u (-x))/2
noncomputable def coeff (u : ℝ → ℝ) (n : ℕ) : ℝ := ∫ x, basis n x * u x
noncomputable def project (o : Bool) (N : ℕ) (u : ℝ → ℝ) : ℝ → ℝ :=
  ∑ j ∈ Finset.range N, coeff u (degree o j) • basis (degree o j)
noncomputable def alpha (o : Bool) (u : ℝ → ℝ) : I → ℝ :=
  fun i => coeff (component o u) (degree o i)
noncomputable def low (o : Bool) (u : ℝ → ℝ) : ℝ → ℝ :=
  ∑ i : I, alpha o u i • basis (degree o i)
noncomputable def tail (o : Bool) (u : ℝ → ℝ) : ℝ → ℝ := component o u - low o u
noncomputable def band (o : Bool) (u : ℝ → ℝ) : I → ℝ :=
  fun i => coeff (tail o u) (degree o (32+i))
noncomputable def far (o : Bool) (u : ℝ → ℝ) : H :=
  embed (tail o u - ∑ i : I, band o u i • basis (degree o (32+i)))
noncomputable def col (o : Bool) (i : I) : ℝ → ℝ :=
  RHWeilColumnCandidate.column halfWidth (basisPoly (degree o i))
noncomputable def columnResidual (o : Bool) (i : I) : H :=
  embed (col o i - project o 64 (col o i))
noncomputable def mixed (o : Bool) (u : ℝ → ℝ) (i : I) : ℝ :=
  ∑ j : I, alpha o u j * (∫ x, col o j x * basis (degree o (32+i)) x)
noncomputable def compare (u : ℝ → ℝ) : ℝ :=
  (RHComparisonEnergy.energy halfWidth (fun x => (u x : ℂ))).toReal
noncomputable def eta (o : Bool) : ℝ := if o then eta_odd_bound else eta_even_bound
noncomputable def tau (o : Bool) : ℝ := if o then tau_odd_bound else tau_even_bound
noncomputable def dN (o : Bool) : ℝ := if o then d64_odd_lower else d64_even_lower
noncomputable def dM (o : Bool) : ℝ := if o then d128_odd_lower else d128_even_lower

def Test (u : ℝ → ℝ) : Prop := ContDiff ℝ 2 u ∧ ∀ x, u x ≠ 0 → |x| ≤ halfWidth

/-- Numerical preprocessing data, shared by every obligation. No positivity fields. -/
structure Parameters where
  B : Bool → Matrix I I ℝ
  coordinates : Bool → (ℝ → ℝ) → I → ℝ
  shift : Bool → ℝ
  weights : Bool → I → ℝ

/-- G1: actual finite-energy residual lower bound. Not full test positivity. -/
def G1 (P : Parameters) : Prop := ∀ o u, Test u →
  MemLp (tail o u) 2 volume ∧
  RHFormDomain.energy (fun x => (tail o u x : ℂ)) < ⊤ ∧
  compare (tail o u) + P.shift o * ‖embed (tail o u)‖^2 ≤ targetQ_real (tail o u)

/-- G2: the exact mixed-form representation with the explicit 0378 columns.
For the concrete parameters this is proved in `RHG2Final0489.g2`. -/
def G2 (P : Parameters) : Prop :=
  (∀ o i, MemLp (col o i) 2 volume ∧
    MemLp (col o i - project o 64 (col o i)) 2 volume) ∧
  ∀ o u, Test u →
  (targetQ_real (component o u) - targetQ_real (low o u) - targetQ_real (tail o u))/2 =
    (∑ i : I, mixed o u i * band o u i) +
    inner ℝ (residual_vector (columnResidual o) (P.B o *ᵥ P.coordinates o u)) (far o u)

/-- G3 refines the real/complex and projection adapters.
The band-plus-far comparison bound is stronger than the old single H_N bound;
its abstract source is ActualTail.finite_comparison_tail. -/
def G3 (P : Parameters) : Prop := ∀ o u, Test u →
  P.B o *ᵥ P.coordinates o u = alpha o u ∧
  (component o u ≠ 0 → embed (component o u) ≠ 0) ∧
  (∑ i : I, (band o u i)^2) + ‖far o u‖^2 = ‖embed (tail o u)‖^2 ∧
  (∑ i : I, ((harmonic (degree o (32+i)) : ℝ) + P.shift o) * (band o u i)^2) +
    ((harmonic (degree o 64) : ℝ) + P.shift o) * ‖far o u‖^2 ≤
    compare (tail o u) + P.shift o * ‖embed (tail o u)‖^2

/-- G4: the same analytic weights contain positive, fixed rational tail bounds. -/
def G4 (P : Parameters) : Prop := ∀ o,
  (∀ i, dN o ≤ P.weights o i) ∧
  (∀ i, P.weights o i ≤ (harmonic (degree o (32+i)) : ℝ) + P.shift o) ∧
  dM o ≤ (harmonic (degree o 64) : ℝ) + P.shift o

def G5 (P : Parameters) : Prop := ∀ o u, Test u →
  (1-eta o) * (∑ i : I, (P.coordinates o u i)^2) ≤
    targetQ_real (low o u) - ∑ i : I, (mixed o u i)^2 / P.weights o i

def G6 (P : Parameters) : Prop := ∀ o,
  Matrix.trace ((1/dM o) • ((P.B o)ᵀ * residual_gram_matrix (columnResidual o) * P.B o)) ≤ tau o

lemma dN_pos (o) : 0 < dN o := by
  cases o <;> simp only [dN, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact even_d64_pos | exact odd_d64_pos
lemma dM_pos (o) : 0 < dM o := by
  cases o <;> simp only [dM, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact even_d128_pos | exact odd_d128_pos
lemma dN_le_dM (o) : dN o ≤ dM o := by
  cases o <;> simp only [dN, dM, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact even_d_mono | exact odd_d_mono
lemma margin_pos (o) : 0 < 1-eta o-tau o := by
  cases o
  · have := even_schur_margin; dsimp [eta,tau]; linarith
  · have := odd_schur_margin; dsimp [eta,tau]; linarith
lemma q_zero : targetQ_real 0 = 0 := by
  unfold targetQ_real RHAutocorrEnergy.spatialEnergy RH_LiteratureBridge.real_autocorr
  simp

lemma weighted_tail (P : Parameters) (h1 : G1 P) (h3 : G3 P) (h4 : G4 P)
    (o) (u) (hu : Test u) :
    (∑ i : I, P.weights o i * (band o u i)^2) + dM o * ‖far o u‖^2 ≤
      targetQ_real (tail o u) := by
  have hb := Finset.sum_le_sum (fun (i : I) (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right ((h4 o).2.1 i) (sq_nonneg (band o u i)))
  have hz := mul_le_mul_of_nonneg_right (h4 o).2.2 (sq_nonneg ‖far o u‖)
  exact (add_le_add hb hz).trans ((h3 o u hu).2.2.2.trans (h1 o u hu).2.2)

/-- The Schur hQ hypothesis is derived here, never assumed by the endpoint. -/
lemma schur_input (P : Parameters) (h1 : G1 P) (h2 : G2 P) (h3 : G3 P) (h4 : G4 P)
    (o) (u) (hu : Test u) :
    targetQ_real (low o u) +
    (∑ i : I, (2 * mixed o u i * band o u i + P.weights o i * (band o u i)^2)) +
    2 * inner ℝ (residual_vector (columnResidual o) (P.B o *ᵥ P.coordinates o u)) (far o u) +
    dM o * ‖far o u‖^2 ≤ targetQ_real (component o u) := by
  have ht := weighted_tail P h1 h3 h4 o u hu
  have hm := h2.2 o u hu
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at ⊢
  linarith

lemma component_positive (P : Parameters) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (o) (u) (hu : Test u) (hn : component o u ≠ 0) :
    0 < targetQ_real (component o u) := by
  have hd : ∀ i, 0 < P.weights o i := fun i => (dN_pos o).trans_le ((h4 o).1 i)
  have hs : 0 ≤ ∑ i : I, (P.coordinates o u i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hc : (∑ i : I, (P.coordinates o u i)^2) = 0
  · have hc0 : P.coordinates o u = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg (P.coordinates o u j))).mp hc i (Finset.mem_univ i)
      exact (sq_eq_zero_iff).mp hi
    have ha : alpha o u = 0 := by
      rw [← (h3 o u hu).1, hc0]; simp
    have hp : low o u = 0 := by simp [low, ha]
    have hr : tail o u = component o u := by simp [tail, hp]
    have hz : 0 < ‖embed (tail o u)‖^2 := by
      rw [hr]; exact sq_pos_of_pos (norm_pos_iff.mpr ((h3 o u hu).2.1 hn))
    have ht := weighted_tail P h1 h3 h4 o u hu
    have hb := Finset.sum_le_sum (fun (i : I) (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right ((h4 o).1 i) (sq_nonneg (band o u i)))
    have hf := mul_le_mul_of_nonneg_right (dN_le_dM o) (sq_nonneg ‖far o u‖)
    have hw : dN o * ‖embed (tail o u)‖^2 ≤ targetQ_real (tail o u) := by
      calc
        _ = (∑ i : I, dN o * (band o u i)^2) + dN o * ‖far o u‖^2 := by
          rw [← (h3 o u hu).2.2.1, mul_add, Finset.mul_sum]
        _ ≤ _ := (add_le_add hb hf).trans ht
    rw [hr] at hw hz
    exact (mul_pos (dN_pos o) hz).trans_le hw
  · have hh := certificate_from_gram_trace (P.weights o) (mixed o u) (band o u)
      hd (columnResidual o) (P.B o) (P.coordinates o u) (far o u)
      (dM_pos o) (h6 o) rfl (schur_input P h1 h2 h3 h4 o u hu) (h5 o u hu)
    exact (mul_pos (margin_pos o) (lt_of_le_of_ne hs (Ne.symm hc))).trans_le hh

lemma component_nonnegative (P : Parameters) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (o) (u) (hu : Test u) : 0 ≤ targetQ_real (component o u) := by
  by_cases hn : component o u = 0
  · rw [hn, q_zero]
  · exact (component_positive P h1 h2 h3 h4 h5 h6 o u hu hn).le

lemma real_positive (P : Parameters) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (u) (hu : Test u) (hn : u ≠ 0) : 0 < targetQ_real u := by
  have he := component_nonnegative P h1 h2 h3 h4 h5 h6 false u hu
  have ho := component_nonnegative P h1 h2 h3 h4 h5 h6 true u hu
  have hs := targetQ_real_parity_split_of_test halfWidth_pos u
    (hu.1.of_le (by norm_num)) hu.2
  change targetQ_real u = targetQ_real (component false u) + targetQ_real (component true u) at hs
  rw [hs]
  by_cases hne : component false u ≠ 0
  · exact add_pos_of_pos_of_nonneg (component_positive P h1 h2 h3 h4 h5 h6 false u hu hne) ho
  · have hno : component true u ≠ 0 := by
      intro hz
      apply hn
      funext x
      have hx := congr_fun (not_ne_iff.mp hne) x
      have hy := congr_fun hz x
      dsimp [component] at hx hy
      change u x = 0
      linarith
    exact add_pos_of_nonneg_of_pos he (component_positive P h1 h2 h3 h4 h5 h6 true u hu hno)

/-- Conditional form: G1–G6 are hypotheses; there is no positivity premise. The concrete instances are supplied in `RHFinalAll0524`. -/
theorem target_log5_of_gaps (P : Parameters)
    (h1 : G1 P) (h2 : G2 P) (h3 : G3 P) (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re := by
  have hp : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
      (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → u ≠ 0 → 0 < targetQ_real u :=
    fun u hu hus hun => real_positive P h1 h2 h3 h4 h5 h6 u ⟨hu, hus⟩ hun
  have hz : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
      (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → 0 ≤ targetQ_real u := by
    intro u hu hus
    by_cases hun : u = 0
    · rw [hun, q_zero]
    · exact (hp u hu hus hun).le
  exact RHTargetLog5.target_log5_endpoint f hf hs hn
    (fun hne => targetQ_pos_of_real_pos f hf hs hne hp hz)
end
end RHConditionalLog5
