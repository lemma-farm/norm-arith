module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.RadialSobolevClosure
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
@[expose] public section
/-! # Weak gradients and closability for the Ginibre radial completion

Write `ρ` for the concrete, unnormalised real Lebesgue density. Testing with
`ρ ψ` avoids division by the density at collisions. The adjoint test is
`ρ ∂ψ + 2 (∂ρ) ψ`. These identities describe the distributional derivative of
`ρ² u`, and determine the gradient uniquely because `ρ > 0` almost everywhere
for the Ginibre measure. They do not assert the reverse approximation theorem
from an independently defined weak Sobolev space to the radial core.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
def ginibreCoordinateDirection {n : ℕ} (k : Fin n × Fin 2) : Configuration n :=
  if k.2 = 0 then realCoordinateDirection k.1 else imaginaryCoordinateDirection k.1
end
end GinibrePoincare
