module
public import Mathlib.Topology.MetricSpace.Isometry
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Ambient.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kinetic spacetime points

This module gives an explicit carrier for kinetic spacetime. Its fields make
the time, position, and velocity coordinate order visible in every theorem
surface.

## Main definitions

* `KineticPoint d` is a kinetic spacetime point with time, position, and
  velocity coordinates.
* `KineticPoint.homeomorphProd d` identifies this explicit carrier with
  `ℝ × (PDE.Vec d × PDE.Vec d)` for standard topology infrastructure.

## Implementation note

The transported product metric supplies only the ordinary topology and
uniformity used by sets, continuity, and compactness. It is not the
manuscript's Euclidean kinetic geometry; Euclidean norms and balls must use
the explicit `PDEFoundation` API.
-/
@[expose] public section
namespace HypoellipticAleksandrov
/-- A point of kinetic spacetime in dimension `d`. -/
@[ext]
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : PDE.Vec d
  /-- Velocity coordinate. -/
  velocity : PDE.Vec d
/-- The explicit coordinate equivalence with the standard nested product carrier. -/
def KineticPoint.equivProd (d : ℕ) :
    KineticPoint d ≃ ℝ × (PDE.Vec d × PDE.Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by
    ext <;> rfl
  right_inv z := by
    rcases z with ⟨t, x, v⟩
    rfl
/-- The standard product metric transported to the explicit coordinate carrier.

This is only topology and uniformity infrastructure, not manuscript round
Euclidean geometry. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d)
    (KineticPoint.equivProd d).injective inferInstance
end HypoellipticAleksandrov
