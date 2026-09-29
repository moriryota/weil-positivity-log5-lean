import ConditionalLog5
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
open MeasureTheory Set
namespace RHG3RealEmbedding
open RHConditionalLog5

lemma component_continuous (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Continuous (component o u) := by
  have hc := hu.1.continuous
  cases o <;> dsimp [component] <;> fun_prop

lemma component_support (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ∀ x, component o u x ≠ 0 → |x| ≤ RHLog5Bridge.halfWidth := by
  intro x hx
  by_contra h
  have h0 : u x = 0 := by
    by_contra hn
    exact h (hu.2 x hn)
  have h1 : u (-x) = 0 := by
    by_contra hn
    exact h (by simpa using hu.2 (-x) hn)
  cases o <;> simp [component, h0, h1] at hx

theorem component_memLp (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    MemLp (component o u) 2 volume :=
  (component_continuous o u hu).memLp_of_hasCompactSupport
    (RHAutocorrEnergy.compact_real (component_support o u hu))

theorem component_embed_ne_zero (o : Bool) (u : ℝ → ℝ) (hu : Test u)
    (hn : component o u ≠ 0) : embed (component o u) ≠ 0 := by
  intro hz
  have hm := component_memLp o u hu
  have he : embed (component o u) = hm.toLp (component o u) := by simp [embed, hm]
  rw [he] at hz
  have hae : component o u =ᵐ[volume] 0 := by
    have hrep := hm.coeFn_toLp
    rw [hz] at hrep
    exact hrep.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  exact hn (((component_continuous o u hu).ae_eq_iff_eq volume continuous_zero).mp hae)
end RHG3RealEmbedding
