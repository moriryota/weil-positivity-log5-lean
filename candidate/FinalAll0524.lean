import Final0524
import AssemblyAll0525

/-! # 0524: unconditional G6c for the concrete parameters and the fixed-width log 5 target.
Inputs: `RHAssembly0525.assembly` (0525), ClaimA/ColParity (0520), `numBound`, G5c (0512).
RH itself is not claimed. -/

namespace RHFinalAll0524

theorem G6c_concrete : RHCaps0494.G6c RHConcreteParameters.concrete RHT5Final0512.capsNew :=
  RHFinal0524.G6c_of_assembly RHAssembly0525.assembly

theorem target_log5_concrete
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHFinal0524.target_log5_of_assembly RHAssembly0525.assembly f hf hs hn

end RHFinalAll0524

