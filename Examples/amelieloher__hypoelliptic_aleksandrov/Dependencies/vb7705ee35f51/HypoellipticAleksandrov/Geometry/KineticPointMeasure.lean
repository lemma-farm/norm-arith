module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Geometry.KineticPoint
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Lebesgue measure on kinetic points

The coordinate equivalence identifies kinetic volume with product Lebesgue
measure in the literal order (t,x,v), without any normalization factor.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov
open MeasureTheory
end HypoellipticAleksandrov
