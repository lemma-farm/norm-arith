import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyStoppingRecursion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite signed-sum and dyadic prefix estimates for Rademacher--Menshov

The signed-sum hypothesis used in KL18 (2.8) is kept explicit. In particular,
no orthogonality of the actual oscillatory pieces is silently assumed.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyRademacherMenshov
set_option autoImplicit false
section L2
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
end L2
end KrauseLaceyRademacherMenshov
end QuadraticCarleson
