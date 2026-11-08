module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Literal stationary geometry for Appendix C

The gauge uses the Euclidean squared norms, independently of the native supremum norm.
The derivative selectors below are total Frechet derivatives on the native product.
Their identification with weak jets on axes is a separate analytic step.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
/-- Native position--velocity coordinates. -/
abbrev XV (d : ℕ) := PDE.Vec d × PDE.Vec d
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
