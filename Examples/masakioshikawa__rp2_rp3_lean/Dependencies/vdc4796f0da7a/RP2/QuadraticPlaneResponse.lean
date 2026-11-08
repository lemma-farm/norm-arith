module
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.QuadraticPlane
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.QuadraticBounds
public import Mathlib
public section
/-!
# The normalized two-axis Ward identity for RP²

Adapted from OpenAI's ClassicalON/RotationWork.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The first and second responses are replaced by their proved quadratic
counterparts; the squared-interaction fourth-order identity supplies the
model-specific step.
-/
namespace RP2.Quadratic
noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]
end SpinSystem
end
end RP2.Quadratic
