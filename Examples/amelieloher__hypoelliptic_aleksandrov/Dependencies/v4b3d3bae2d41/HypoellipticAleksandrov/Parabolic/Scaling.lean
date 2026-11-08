module
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.LocalClassical
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic affine scaling

This file records the exact translation and parabolic-dilation identities for
the forward time--velocity operator.  The affine map itself is defined in
`HarnackGeometry`; this module supplies its differential and the induced local
classical pullback API.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter Set
open scoped MatrixOrder Topology
end HypoellipticAleksandrov.Parabolic
