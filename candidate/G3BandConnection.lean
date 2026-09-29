import ConditionalLog5
import FiniteTail

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix
namespace RHG3BandConnection
open RHConditionalLog5

/-- No new polynomial/basis: coefficients of the actual 0401 tail. -/
noncomputable def massCoeff (o : Bool) (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  (coeff (tail o u) (degree o n))^2

lemma harmonic_mono_real {m n : ℕ} (h : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  have hq : harmonic m ≤ harmonic n := by
    unfold harmonic
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      (by intro i _ _; positivity)
  exact_mod_cast hq

lemma degree_mono (o : Bool) {m n : ℕ} (h : m ≤ n) : degree o m ≤ degree o n := by
  unfold degree
  omega

lemma split64 (a : ℕ → ℝ) (hz : ∀ n, n < 32 → a n = 0) :
    (∑ n ∈ Finset.range 64, a n) = ∑ i : I, a (32+i) := by
  rw [show (64:ℕ) = 32+32 from rfl, Finset.sum_range_add]
  have hl : ∑ n ∈ Finset.range 32, a n = 0 :=
    Finset.sum_eq_zero (fun n hn => hz n (Finset.mem_range.mp hn))
  rw [hl, zero_add]
  exact Finset.sum_range (fun n => a (32+n))

/-- Consumes finite coefficient bounds and Parseval convergence via the existing tail theorem.
It does not assume the desired band-plus-far inequality. -/
theorem band_shift_from_coefficients (P : Parameters) (o : Bool) (u : ℝ → ℝ)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M,
      (harmonic (degree o n) : ℝ) * massCoeff o u n ≤ compare (tail o u))
    (hmass : Tendsto (fun M => ∑ n ∈ Finset.range M, massCoeff o u n)
      atTop (𝓝 (‖embed (tail o u)‖^2)))
    (hzero : ∀ n, n < 32 → coeff (tail o u) (degree o n) = 0)
    (hnorm : (∑ i : I, (band o u i)^2) + ‖far o u‖^2 = ‖embed (tail o u)‖^2) :
    (∑ i : I, ((harmonic (degree o (32+i)) : ℝ)+P.shift o) * (band o u i)^2) +
      ((harmonic (degree o 64) : ℝ)+P.shift o) * ‖far o u‖^2 ≤
      compare (tail o u) + P.shift o * ‖embed (tail o u)‖^2 := by
  have hz : ∀ n, n < 32 → massCoeff o u n = 0 := by
    intro n hn
    simp [massCoeff, hzero n hn]
  have ht := RHFiniteTail.lower_bound (massCoeff o u)
    (fun n => (harmonic (degree o n) : ℝ)) 64 (harmonic (degree o 64))
    (compare (tail o u)) (‖embed (tail o u)‖^2)
    (fun n => sq_nonneg _) (fun n hn => harmonic_mono_real (degree_mono o hn)) hfinite hmass
  have hs := split64 (massCoeff o u) hz
  have hw := split64 (fun n => (harmonic (degree o n) : ℝ) * massCoeff o u n)
    (fun n hn => by rw [hz n hn, mul_zero])
  rw [hs, hw] at ht
  change (∑ i : I, (harmonic (degree o (32+i)) : ℝ) * (band o u i)^2) +
    (harmonic (degree o 64) : ℝ) * (‖embed (tail o u)‖^2 - ∑ i : I, (band o u i)^2) ≤ _ at ht
  have hm : ‖embed (tail o u)‖^2 - ∑ i : I, (band o u i)^2 = ‖far o u‖^2 := by linarith
  rw [hm] at ht
  calc
    _ = ((∑ i : I, (harmonic (degree o (32+i)) : ℝ) * (band o u i)^2) +
        (harmonic (degree o 64) : ℝ) * ‖far o u‖^2) +
        P.shift o * ((∑ i : I, (band o u i)^2) + ‖far o u‖^2) := by
          simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
    _ ≤ compare (tail o u) + P.shift o * ((∑ i : I, (band o u i)^2) + ‖far o u‖^2) :=
      add_le_add ht le_rfl
    _ = _ := by rw [hnorm]

/-- Remaining actual-coordinate inputs; no shifted band lower bound in this contract. -/
def CoefficientInputs (P : Parameters) : Prop := ∀ o u, Test u →
  P.B o *ᵥ P.coordinates o u = alpha o u ∧
  (component o u ≠ 0 → embed (component o u) ≠ 0) ∧
  (∑ i : I, (band o u i)^2) + ‖far o u‖^2 = ‖embed (tail o u)‖^2 ∧
  (∀ M, ∑ n ∈ Finset.range M, (harmonic (degree o n) : ℝ) * massCoeff o u n ≤ compare (tail o u)) ∧
  Tendsto (fun M => ∑ n ∈ Finset.range M, massCoeff o u n) atTop (𝓝 (‖embed (tail o u)‖^2)) ∧
  (∀ n, n < 32 → coeff (tail o u) (degree o n) = 0)

theorem g3_of_coefficient_inputs (P : Parameters) (h : CoefficientInputs P) : G3 P := by
  intro o u hu
  obtain ⟨hc, hn, hm, hf, hs, hz⟩ := h o u hu
  exact ⟨hc, hn, hm, band_shift_from_coefficients P o u hf hs hz hm⟩

/-- Actual application to the unchanged 0401 final theorem. Research inputs remain explicit. -/
theorem target_log5_of_coefficient_inputs (P : Parameters)
    (h1 : G1 P) (h2 : G2 P) (hc : CoefficientInputs P)
    (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  target_log5_of_gaps P h1 h2 (g3_of_coefficient_inputs P hc) h4 h5 h6 f hf hs hn
end RHG3BandConnection
