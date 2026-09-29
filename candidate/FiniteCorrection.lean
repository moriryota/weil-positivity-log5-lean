import DomainLinear
namespace RHFormDomain
open MeasureTheory Set
open scoped BigOperators

/-- Any finite correction by domain vectors preserves the domain.
Membership of the actual Legendre vectors is a separate obligation. -/
theorem finite_correction_mem {ι : Type*} {L : ℝ}
    (s : Finset ι) (e : ι → Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (he : ∀ i ∈ s, InDomain L (e i)) (c : ι → ℂ)
    {f : Lp ℂ 2 (volume.restrict (Icc (-L) L))} (hf : InDomain L f) :
    InDomain L (f - ∑ i ∈ s, c i • e i) := by
  apply (formSubmodule L).sub_mem hf
  exact (formSubmodule L).sum_mem (fun i hi => (formSubmodule L).smul_mem (c i) (he i hi))
end RHFormDomain
