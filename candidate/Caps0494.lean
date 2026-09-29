import G2Final0489

/-! # 0494 T2: parametric η/τ caps for G5/G6 (final target statement unchanged)

The fixed constants `eta`/`tau` of `RHConditionalLog5` enter the final argument only through
`margin_pos : 0 < 1 - eta o - tau o` and the generic `certificate_from_gram_trace`.
This file replays `component_positive`/`real_positive`/`target_log5_of_gaps` with caps
`k : Caps` satisfying `0 < 1 - k.eta o - k.tau o`. -/

open MeasureTheory Set
open scoped BigOperators Matrix

namespace RHCaps0494
open RHConditionalLog5 RHTargetFormBinding RHLog5Bridge RHResidualCertificate RHCertificateData

structure Caps where
  eta : Bool → ℝ
  tau : Bool → ℝ
  margin : ∀ o, 0 < 1 - eta o - tau o

def G5c (P : Parameters) (k : Caps) : Prop := ∀ o u, Test u →
  (1 - k.eta o) * (∑ i : I, (P.coordinates o u i)^2) ≤
    targetQ_real (low o u) - ∑ i : I, (mixed o u i)^2 / P.weights o i

def G6c (P : Parameters) (k : Caps) : Prop := ∀ o,
  Matrix.trace ((1/dM o) • ((P.B o)ᵀ * residual_gram_matrix (columnResidual o) * P.B o)) ≤ k.tau o

/-- The old fixed constants form an admissible cap. -/
noncomputable def capsOld : Caps := ⟨eta, tau, margin_pos⟩

theorem G5c_of_G5 {P : Parameters} (h : G5 P) : G5c P capsOld := h
theorem G6c_of_G6 {P : Parameters} (h : G6 P) : G6c P capsOld := h

lemma component_positive_caps (P : Parameters) (k : Caps) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5c P k) (h6 : G6c P k)
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
    exact (mul_pos (k.margin o) (lt_of_le_of_ne hs (Ne.symm hc))).trans_le hh

lemma component_nonnegative_caps (P : Parameters) (k : Caps) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5c P k) (h6 : G6c P k)
    (o) (u) (hu : Test u) : 0 ≤ targetQ_real (component o u) := by
  by_cases hn : component o u = 0
  · rw [hn, q_zero]
  · exact (component_positive_caps P k h1 h2 h3 h4 h5 h6 o u hu hn).le

lemma real_positive_caps (P : Parameters) (k : Caps) (h1 : G1 P) (h2 : G2 P)
    (h3 : G3 P) (h4 : G4 P) (h5 : G5c P k) (h6 : G6c P k)
    (u) (hu : Test u) (hn : u ≠ 0) : 0 < targetQ_real u := by
  have he := component_nonnegative_caps P k h1 h2 h3 h4 h5 h6 false u hu
  have ho := component_nonnegative_caps P k h1 h2 h3 h4 h5 h6 true u hu
  have hs := targetQ_real_parity_split_of_test halfWidth_pos u
    (hu.1.of_le (by norm_num)) hu.2
  change targetQ_real u = targetQ_real (component false u) + targetQ_real (component true u) at hs
  rw [hs]
  by_cases hne : component false u ≠ 0
  · exact add_pos_of_pos_of_nonneg (component_positive_caps P k h1 h2 h3 h4 h5 h6 false u hu hne) ho
  · have hno : component true u ≠ 0 := by
      intro hz
      apply hn
      funext x
      have hx := congr_fun (not_ne_iff.mp hne) x
      have hy := congr_fun hz x
      dsimp [component] at hx hy
      change u x = 0
      linarith
    exact add_pos_of_nonneg_of_pos he (component_positive_caps P k h1 h2 h3 h4 h5 h6 true u hu hno)

/-- Same conclusion as `target_log5_of_gaps`, with G5/G6 at arbitrary admissible caps. -/
theorem target_log5_of_gaps_caps (P : Parameters) (k : Caps)
    (h1 : G1 P) (h2 : G2 P) (h3 : G3 P) (h4 : G4 P) (h5 : G5c P k) (h6 : G6c P k)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re := by
  have hp : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
      (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → u ≠ 0 → 0 < targetQ_real u :=
    fun u hu hus hun => real_positive_caps P k h1 h2 h3 h4 h5 h6 u ⟨hu, hus⟩ hun
  have hz : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
      (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → 0 ≤ targetQ_real u := by
    intro u hu hus
    by_cases hun : u = 0
    · rw [hun, q_zero]
    · exact (hp u hu hus hun).le
  exact RHTargetLog5.target_log5_endpoint f hf hs hn
    (fun hne => targetQ_pos_of_real_pos f hf hs hne hp hz)

/-- Fixed log 5 target from G5/G6 at admissible caps; G1 (0486), G2 (0489), G3, G4 supplied. -/
theorem target_log5_of_G5c_G6c (k : Caps)
    (h5 : G5c RHConcreteParameters.concrete k) (h6 : G6c RHConcreteParameters.concrete k)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  target_log5_of_gaps_caps RHConcreteParameters.concrete k RHG1Adapter0484.g1 RHG2Final0489.g2
    RHSpectralInputs.g3_unconditional RHConcreteParameters.g4 h5 h6 f hf hs hn

end RHCaps0494

