-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.vb8a201c5676e.Hormander.Defs.VectorFieldOp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open SchwartzMap
namespace Hormander
/-- The operator `L = Σ_{i=1}^k Xᵢ² + X₀ + c` acting on complex tempered distributions on `ℝᴺ`,
built from `vectorFieldOp` and multiplication by `c`. Meaningful for coefficients with temperate
growth (in particular `C_c^∞` coefficients, the only case used). -/
def hormanderOp {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  (∑ i : Fin k, (vectorFieldOp (X i.succ)).comp (vectorFieldOp (X i.succ))) +
    vectorFieldOp (X 0) +
    TemperedDistribution.smulLeftCLM ℂ (fun x => ((c x : ℝ) : ℂ))
end Hormander
