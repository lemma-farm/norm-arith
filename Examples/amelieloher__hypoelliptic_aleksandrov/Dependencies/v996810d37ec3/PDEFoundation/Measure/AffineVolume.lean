module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Geometry.Affine
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Translation and dilation of volume

Exact change-of-variable statements for native vectors. These are the
measure-level foundation of all later scale-invariant norms.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
open MeasureTheory
end PDE
