module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coefficient fields and ellipticity

This module fixes the curried time--velocity coefficient convention and the
Mathlib Loewner-order ellipticity predicates.  It also proves the matrix-level
positive-definiteness and determinant consequences of a positive lower bound.
-/
@[expose] public section
open scoped BigOperators ContDiff MatrixOrder Matrix.Norms.Elementwise
open Matrix
open MeasureTheory
namespace HypoellipticAleksandrov
/-- The product measurable-space structure on finite real matrices used for coefficient fields. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance
/-- A real matrix-valued coefficient field, curried in time and velocity. -/
abbrev CoefficientField (d : ℕ) := ℝ → PDE.Vec d → PDE.Mat d
def HasLowerEllipticity {d : ℕ} (lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ t v, lam • (1 : PDE.Mat d) ≤ A t v
namespace HasLowerEllipticity
end HasLowerEllipticity
end HypoellipticAleksandrov
