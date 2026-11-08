module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeVStarPrimitive
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevSeparable
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Canonical affine representative for the reverse-time Gelfand curve

This module identifies the reverse-time Gelfand curve with its dual Bochner
primitive plus its canonical Bochner-average affine constant.  The result is
only an almost-everywhere identity in the spatial Gelfand dual; it supplies no
trace, energy identity, or Hilbert-valued representative.
-/
@[expose] public section
open Filter Function MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet
