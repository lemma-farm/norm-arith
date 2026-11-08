import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceySparseReflection
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HardyLittlewoodBoundaryControl
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exact positive dilation and conjugation of smooth sparse bounds

The change of variables normalizing a nonzero quadratic modulation is an
arbitrary positive dilation, not necessarily a dyadic dilation.  Accordingly
the exact operator identities below use finite sets of actual positive
smooth radii.  The project's rounded-radius maximum is a special case,
but the rounded radii themselves are not asserted to commute with dilation.

The geometric transfer proves the change of variables for the test space,
intervals, major subsets, local averages, sparse forms, and pairings.  No
sparse conclusion or invariance property is postulated.

The final unit input quantifies over arbitrary positive radii.  The existing
unit dyadic-suffix sparse theorem supplies only rounded dyadic radii.  Passing
from that latter input to this one still requires an annular comparison with
a sparse maximal-average bound, or an extension of the unit analytic proof
to arbitrary scale offsets; that additional implication is not assumed here.
-/
open Function MeasureTheory Set
open scoped ENNReal Topology ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
noncomputable section
namespace L0Infinity
end L0Infinity
namespace RealInterval
end RealInterval
namespace KrauseLaceySparseDilation
open KrauseLaceySharpSmoothAdapter QuadraticHilbertMaximalMeasurable
end KrauseLaceySparseDilation
end
end QuadraticCarleson
