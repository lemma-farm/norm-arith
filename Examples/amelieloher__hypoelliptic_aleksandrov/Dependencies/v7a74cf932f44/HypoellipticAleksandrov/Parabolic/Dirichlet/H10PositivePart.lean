module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenPositivePartApproximation
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.H10LevelSet
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive parts in spatial `H¹₀`

This module constructs the positive part of an arbitrary spatial `H¹₀`
graph point on an open set, identifies its weak gradient, and records the
sharp contractions of its value and gradient components.
-/
@[expose] public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
end HypoellipticAleksandrov.Parabolic.Dirichlet
