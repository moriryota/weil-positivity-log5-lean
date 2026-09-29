import Interface0516
import ResidualApprox0494
import ConcreteParameters

/-! # 0524: pinned interface for the final G6c assembly (numeric side ↔ analytic assembly)

* `Gam o i k = ∫ Sx_{deg i} Sx_{deg k}` and `sco o i m = ∫ Sx_{deg i} · basis_{deg m}` (Sx from Interface0516).
* `NumBound δ η τ`: the numeric inequality (proved from the kernel-checked tables for
  `δ = 1/10^14`, `η = 1/10^4`, `τ = 99/100`).
* `AssemblyGoal`: ClaimA + ColParity + NumBound ⇒ for each parity a choice of `W` with the
  `G6c_of_approx` integral bound.
Definitions only. -/

open MeasureTheory Finset

namespace RHInterface0524
open RHConditionalLog5 RHInterface0516

noncomputable def Gam (o : Bool) (i k : I) : ℝ := ∫ x, Sx (degree o i) x * Sx (degree o k) x
noncomputable def sco (o : Bool) (i : I) (m : ℕ) : ℝ := ∫ x, Sx (degree o i) x * basis (degree o m) x

def NumBound (δ η τ : ℝ) : Prop :=
  ∀ o : Bool, (1 / dM o) * ∑ j : I,
    ((1 + η) * (∑ i : I, ∑ k : I, RHConcreteParameters.concrete.B o i j * RHConcreteParameters.concrete.B o k j * Gam o i k -
        ∑ m ∈ range 64, (∑ i : I, RHConcreteParameters.concrete.B o i j * sco o i m) ^ 2) +
      (1 + 1 / η) * (2 * RHLog5Bridge.halfWidth) * (δ * ∑ i : I, |RHConcreteParameters.concrete.B o i j|) ^ 2) ≤ τ

def AssemblyGoal : Prop :=
  ∀ δ η τ : ℝ, 0 ≤ δ → 0 < η → ClaimA δ → ColParity → NumBound δ η τ →
    ∀ o : Bool, ∃ W : ℕ → I → ℝ, (1 / dM o) * ∑ j : I, ∫ x,
      (∑ i : I, RHConcreteParameters.concrete.B o i j * col o i x -
        ∑ m ∈ range 64, W m j * basis (degree o m) x) ^ 2 ≤ τ

end RHInterface0524
