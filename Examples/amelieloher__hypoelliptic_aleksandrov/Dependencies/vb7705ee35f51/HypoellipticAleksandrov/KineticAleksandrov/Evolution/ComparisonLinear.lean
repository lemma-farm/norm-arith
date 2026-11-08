module
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Linearity of the viscous transported operator

The operator `L_ε` is linear on functions that are slice regular at the point
in the sense of `IsSliceRegularAt`.  These identities are used to apply the
maximum argument to differences of a solution and a barrier.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology
end HypoellipticAleksandrov.KineticAleksandrov
