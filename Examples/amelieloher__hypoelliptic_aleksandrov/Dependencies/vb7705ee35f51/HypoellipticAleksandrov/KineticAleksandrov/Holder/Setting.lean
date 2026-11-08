module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Proposed Section 6 setting

Predicates for companion paper, Section 9.
The operator, affine map, quasi-distance and forward stack are reused from
KineticAleksandrov.Operator and Geometry with their usual meanings.
Smoothness is expressed in the existing product coordinates, not through a
new differential structure on KineticPoint.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory
open scoped ENNReal
end HypoellipticAleksandrov.KineticAleksandrov.Holder
