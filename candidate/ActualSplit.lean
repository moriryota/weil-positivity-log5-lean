import QuadrantSplit
import DomainLinear
open MeasureTheory Set
open scoped ENNReal
namespace RHEnergySplit
open RHFormDomain

noncomputable def internal (L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x in Icc (-L) L, ∫⁻ y in Icc (-L) L,
    kernel (x-y) * ENNReal.ofReal (‖f x-f y‖^2)
noncomputable def cross (L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x in Icc (-L) L, ∫⁻ y in (Icc (-L) L)ᶜ,
    kernel (x-y) * ENNReal.ofReal (‖f x‖^2)

theorem energy_split (L : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    energy (extend L f) = (4:ℝ≥0∞)⁻¹ * (internal L f + 2 * cross L f) := by
  let I := Icc (-L) L
  let g := extend L f
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => kernel (z.1-z.2) * ENNReal.ofReal (‖g z.1-g z.2‖^2)
  have hg : Measurable g := hf.indicator measurableSet_Icc
  have hF : Measurable F := measurable_density hg
  have hs : ∀ x y, F (x,y) = F (y,x) := by
    intro x y
    simp only [F, kernel, abs_sub_comm x y, norm_sub_rev (g x) (g y)]
  have hz : ∀ x ∉ I, ∀ y ∉ I, F (x,y) = 0 := by
    intro x hx y hy
    have gx : g x = 0 := indicator_of_notMem hx f
    have gy : g y = 0 := indicator_of_notMem hy f
    simp [F,gx,gy]
  have h := quadrant_split I measurableSet_Icc F hF hs hz
  have hin : (∫⁻ x in I, ∫⁻ y in I, F (x,y)) = internal L f := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro x hx
    apply setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    have gx : g x = f x := indicator_of_mem hx f
    have gy : g y = f y := indicator_of_mem hy f
    simp only [F,gx,gy]
  have hcross : (∫⁻ x in I, ∫⁻ y in Iᶜ, F (x,y)) = cross L f := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro x hx
    apply setLIntegral_congr_fun measurableSet_Icc.compl
    intro y hy
    have hy' : y ∉ I := hy
    have gx : g x = f x := indicator_of_mem hx f
    have gy : g y = 0 := indicator_of_notMem hy' f
    simp [F,gx,gy]
  rw [hin,hcross] at h
  exact congrArg (fun v : ℝ≥0∞ => (4:ℝ≥0∞)⁻¹*v) h

theorem actual_energy_split (L : ℝ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    intervalEnergy L f = (4:ℝ≥0∞)⁻¹ * (internal L f + 2 * cross L f) :=
  energy_split L f (Lp.stronglyMeasurable f).measurable
end RHEnergySplit
