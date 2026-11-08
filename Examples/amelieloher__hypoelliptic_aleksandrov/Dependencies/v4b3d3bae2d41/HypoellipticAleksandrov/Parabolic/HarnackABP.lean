module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.ABP
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.ExponentialConjugation
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.LocalGluing
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.ScalingMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The local ABP bridge for the parabolic Harnack argument

This file proves the translated, radius-one-half ABP consequence used in
Krylov--Safonov Lemma 3.2.  It turns local classical data on the inner
cylinder into the globally regular data required by the unit ABP
estimate, removes the zeroth-order term by exponential conjugation, and then
uses the exact parabolic restricted-norm scaling formula.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped MatrixOrder Topology
end HypoellipticAleksandrov.Parabolic
