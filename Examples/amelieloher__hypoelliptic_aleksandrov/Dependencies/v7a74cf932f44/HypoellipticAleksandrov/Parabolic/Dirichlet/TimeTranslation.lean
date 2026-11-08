module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Local translation continuity for reverse-time Bochner spaces

This module obtains local literal-representative `L²` translation continuity
from the continuous domain-add action on ambient `Lp`.  The local statements
use a zero extension only as an `Lp` representative; they make no derivative
claim for that extension.
-/
@[expose] public section
open Filter MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet
