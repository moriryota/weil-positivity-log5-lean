import CenteredConstant
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set
namespace RHBoundedWindow

def BoundedOn (L : ℝ) (p : ℝ → ℂ) (M : ℝ) : Prop :=
  ∀ x ∈ Icc (-L) L, ‖p x‖ ≤ M

def LipschitzBoundOn (L : ℝ) (p : ℝ → ℂ) (M : ℝ) : Prop :=
  ∀ x ∈ Icc (-L) L, ∀ y ∈ Icc (-L) L, ‖p x - p y‖ ≤ M * |x-y|

def PointwiseBound (L : ℝ) (p : ℝ → ℂ) (M0 M1 : ℝ) : Prop :=
  ∀ x y : ℝ,
    ‖RHFormDomain.extend L p x - RHFormDomain.extend L p y‖^2 ≤
    M1^2 * (2*L) * min |x-y| (2*L) * (Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ)) x
    + M0^2 * ‖RHFormDomain.extend L (fun _ : ℝ => (1:ℂ)) x -
      RHFormDomain.extend L (fun _ : ℝ => (1:ℂ)) y‖^2

end RHBoundedWindow
