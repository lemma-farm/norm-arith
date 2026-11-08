import Examples.Inspectordaniel__metric_surgery_lean.Dependencies.vccfcdd464a69.Tablet.Curve
set_option autoImplicit false
-- [TABLET NODE: IsClosedCurve]
/-- `γ` is a closed curve: its two endpoints coincide. -/
def IsClosedCurve {E : Type*} [MetricSpace E] (γ : Curve E) : Prop :=
-- BODY
  γ.toFun γ.len = γ.toFun 0
