module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic time--velocity geometry

This module fixes the explicit Euclidean time--velocity cylinders and their
forward parabolic boundary. The terminal open-ball face is deliberately not a
boundary component.
-/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
/-- Time--velocity points in dimension `d`. -/
abbrev TimeVelocity (d : ℕ) := ℝ × PDE.Vec d
/-- The analytic interior `(0, T) × B₁(y₀)` of a parabolic cylinder. -/
def parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioo 0 T ×ˢ PDE.euclideanBall y₀ 1
@[simp] theorem mem_parabolicInterior_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicInterior T y₀ ↔
      0 < t ∧ t < T ∧ v ∈ PDE.euclideanBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    exact ⟨hzero, hT, hv⟩
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩
theorem measurableSet_parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicInterior T y₀) :=
  measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall y₀ 1)
end HypoellipticAleksandrov.Parabolic
