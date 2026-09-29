import ResidualMembership
namespace RHResidualMembership
open RHConditionalLog5
/-- The two remaining G1 energy inputs; MemLp is supplied from Test. -/
def G1EnergyInputs (P : Parameters) : Prop := ∀ o u, Test u →
  RHFormDomain.energy (fun x => (tail o u x : ℂ)) < ⊤ ∧
  compare (tail o u) + P.shift o * ‖embed (tail o u)‖^2 ≤
    RHTargetFormBinding.targetQ_real (tail o u)
theorem g1_of_energy_inputs (P : Parameters) (h : G1EnergyInputs P) : G1 P := by
  intro o u hu
  exact ⟨tail_memLp o u hu, h o u hu⟩
end RHResidualMembership
