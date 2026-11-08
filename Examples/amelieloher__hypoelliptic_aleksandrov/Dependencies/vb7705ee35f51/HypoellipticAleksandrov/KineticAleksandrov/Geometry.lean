module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Geometry.KineticPoint
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Geometry for the kinetic Aleksandrov principle

This module records the source kinetic cylinders, their inflow boundary, the
kinetic affine map, the explicit Euclidean quasi-distance, and forward stacks.
The Euclidean geometry is supplied by `PDEFoundation`; the metric transported
to `KineticPoint` is used only for the topological closure in the boundary.
-/
@[expose] public section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set
end HypoellipticAleksandrov.KineticAleksandrov
