import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryReductionLimit
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.MetricSpace.Cauchy
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Principal-value closure from the uniform maximal weak estimate

Smooth compactly supported functions are approximated using Mathlib's actual
`L¹` density theorem. The sole classical input is the uniform weak estimate
for the genuine ordinary Hilbert maximal truncation on `L0Infinity`.
-/
open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology
namespace QuadraticCarleson
namespace HilbertPrincipalValueClosure
open HilbertFiniteTruncationWeakOneOne OscillatoryReduction
set_option autoImplicit false
end HilbertPrincipalValueClosure
end QuadraticCarleson
