import Examples.Inspectordaniel__metric_surgery_lean.Dependencies.vccfcdd464a69.Tablet.curveRestrict
import Examples.Inspectordaniel__metric_surgery_lean.Dependencies.vccfcdd464a69.Tablet.curveWrapRestrict
import Examples.Inspectordaniel__metric_surgery_lean.Dependencies.vccfcdd464a69.Tablet.IsClosedCurve
set_option autoImplicit false
open Set
-- [TABLET NODE: curveArc]
/-- The counter-clockwise circular arc `γ|_{[t,t']}` of a closed curve, uniform in the order of
`t,t'` (paper lines 556-569): the ordinary restriction when `t ≤ t'`, and the wrap-around
restriction when `t' < t`. This is exactly the object `BasicCut` already case-splits on
internally. -/
noncomputable def curveArc {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) : Curve E :=
-- BODY
  if h : t ≤ t' then curveRestrict γ t t' ht0 h ht'l
  else curveWrapRestrict γ t t' hcl ht0 htl ht'0 (not_le.mp h)
