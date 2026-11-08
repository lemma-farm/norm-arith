module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Defs
public import Mathlib.MeasureTheory.Integral.Pi
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Product functions on phase space

A function `y ↦ ∏ i, f (y.1 i, y.2 i)` on `EvolutionAmbientState d = Vec d × Vec d` is integrable
when `f` is integrable on `ℝ × ℝ`, and its integral is `(∫ f) ^ d`. This is the coordinate
independence used to reduce the Gaussian flow to the two-dimensional factor `φ_h`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
