module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePartContinuity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive-part dual-pairing convergence

This module packages the finite-measure \(L^2\) convergence argument for the
positive-part map and its induced dual pairings.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
end HypoellipticAleksandrov.Parabolic.Dirichlet
