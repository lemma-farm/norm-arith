import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The genuine frozen block input belongs to the paper's test domain

Every stopping cell meets the support of the original input and has length
at most the data-dependent root length. Thus all stopping cells lie in one
bounded enlargement of a compact set supporting the original input. Exact
disjointness also gives a pointwise `2 A_k` bound for any frozen scale block,
with no factor depending on its number of scales.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryFrozenInputL0
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CanonicalScaleAtoms
open PositiveEndpointOptimization LacunaryMiddleRange LacunaryMiddleOperator
set_option autoImplicit false
end LacunaryFrozenInputL0
end QuadraticCarleson
