module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.ABP
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.ExponentialConjugation
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.LocalGluing
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.ScalingMeasure
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
/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine {d : ℕ} (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)
/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0
end HypoellipticAleksandrov.Parabolic
