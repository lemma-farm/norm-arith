module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compact cutoff gluing for local parabolic data

This module turns scalar and coefficient data given on an open neighbourhood
of a compact set into literal global data by multiplication with a smooth
cutoff. It also records the pointwise locality of the parabolic operator. No
ellipticity or parabolic estimate is asserted here.
-/
@[expose] public section
open Filter Function Set
open scoped ContDiff Manifold Topology
namespace HypoellipticAleksandrov.Parabolic
end HypoellipticAleksandrov.Parabolic
