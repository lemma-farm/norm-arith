module
-- Reversible module-visibility port of the audited development.
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.LargeValueDefinitions
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density
/-- The stronger fixed cutoff required only for the comparison step. -/
structure ComparisonCutoff extends ReflectionCutoff where
  nonneg : ∀ x, 0 ≤ toFun x
  one_on : ∀ x ∈ Icc (1 : ℝ) 4, toFun x = 1
instance : CoeFun ComparisonCutoff (fun _ => ℝ → ℝ) := ⟨fun w => w.toFun⟩
end MathCollab.Density
