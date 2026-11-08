module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Ambient.Basic
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
end HypoellipticAleksandrov.Parabolic
