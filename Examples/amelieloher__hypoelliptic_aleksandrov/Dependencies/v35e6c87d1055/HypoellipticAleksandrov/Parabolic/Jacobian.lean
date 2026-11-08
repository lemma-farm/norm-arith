module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.ContactMap
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.LinearAlgebra.DeterminantTrace
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic normal-map Jacobian

This module differentiates the parabolic normal map in the product carrier
`TimeVelocity d`.  The `timeVelocityCoordinates` orders time last,
whereas the block calculation here uses a private time-first coordinate display.
Their determinant relation is proved through conjugation, not asserted by
definitional equality.  The raw velocity Jacobian keeps the mixed derivatives
in their genuine order until an explicit `C²` Schwarz bridge replaces it with
`velocityHessian`.

The resulting determinant identity needs only pointwise nonnegativity of the
time derivative and positive semidefiniteness of the negative velocity Hessian;
it has no contact-set premise.  The module also proves the exact pointwise
source bound used by the parabolic ABP argument.  The determinant calculation
uses a determinant-one row operation and therefore requires no Hessian inverse,
also when `d = 0`.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder
open Matrix
/-! ## The actual Fréchet derivative -/
end HypoellipticAleksandrov.Parabolic
