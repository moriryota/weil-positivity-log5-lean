import G3BandConnection
import RealEmbedding
open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix
namespace RHG3Integrated
open RHConditionalLog5 RHG3BandConnection RHG3RealEmbedding

/-- Remaining geometry/coefficient inputs. Test nondegeneracy is now proved. -/
def GeometryInputs (P : Parameters) : Prop := ∀ o u, Test u →
  P.B o *ᵥ P.coordinates o u = alpha o u ∧
  (∑ i : I, (band o u i)^2) + ‖far o u‖^2 = ‖embed (tail o u)‖^2 ∧
  (∀ M, ∑ n ∈ Finset.range M, (harmonic (degree o n) : ℝ) * massCoeff o u n ≤ compare (tail o u)) ∧
  Tendsto (fun M => ∑ n ∈ Finset.range M, massCoeff o u n) atTop (𝓝 (‖embed (tail o u)‖^2)) ∧
  (∀ n, n < 32 → coeff (tail o u) (degree o n) = 0)


theorem coefficient_inputs_of_geometry (P : Parameters) (h : GeometryInputs P) : CoefficientInputs P := by
  intro o u hu
  obtain ⟨hc, hm, hf, hs, hz⟩ := h o u hu
  exact ⟨hc, component_embed_ne_zero o u hu, hm, hf, hs, hz⟩

theorem g3_of_geometry (P : Parameters) (h : GeometryInputs P) : G3 P :=
  g3_of_coefficient_inputs P (coefficient_inputs_of_geometry P h)

theorem target_log5_of_geometry (P : Parameters)
    (h1 : G1 P) (h2 : G2 P) (hg : GeometryInputs P)
    (h4 : G4 P) (h5 : G5 P) (h6 : G6 P)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  target_log5_of_gaps P h1 h2 (g3_of_geometry P hg) h4 h5 h6 f hf hs hn
end RHG3Integrated
