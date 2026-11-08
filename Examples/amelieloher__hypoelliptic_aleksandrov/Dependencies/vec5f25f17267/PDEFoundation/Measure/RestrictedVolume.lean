module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Geometry.ConvexDomain
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Restricted Lebesgue volume

One restricted-volume convention for every later `Lp`, Sobolev, and weak PDE
module.
-/
@[expose] public section
namespace PDE
/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U
namespace IsOpenBoundedConvexDomain
end IsOpenBoundedConvexDomain
namespace IsSobolevRegularDomain
end IsSobolevRegularDomain
end PDE
