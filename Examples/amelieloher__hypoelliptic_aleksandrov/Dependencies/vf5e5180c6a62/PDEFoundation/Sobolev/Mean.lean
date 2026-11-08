module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.AffineVolume
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.Jensen
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.NormalizedLp
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integral means on native vector domains

The compatibility definitions of zero mean and integral average are kept
separate.  `MeanZeroOn` remains meaningful without dividing by the volume;
results using `integralAverage` state positive finite volume explicitly when
that condition matters.
-/
@[expose] public section
namespace PDE
open MeasureTheory
open scoped ENNReal Pointwise
end PDE
