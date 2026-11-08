/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureEntryScheduleBlocks
public import Mathlib
set_option autoImplicit false
/-!
# Actual inner intervals and marked split points

The split point minimizes the marked values among the full blocks inside
`[a+q,t-q]`. Their actual union is an interval, contains `[a+2q,t-2q]`, and
the profile on that union lies above the split value.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
/-- The actual blocks contained in the shrunken interval `[a+q,t-q]`. -/
def profileInnerBlocks (q N a t : ℕ) : Finset ℕ :=
  (Finset.range (N / q + 1)).filter
    (fun b ↦ a + q ≤ profileBlockStart q b ∧ profileBlockEnd q N b ≤ t - q)
/-- The actual marked candidates for the split point. -/
def profileSplitCandidates (A : ℕ → ℝ) (q N a t : ℕ) : Finset ℕ :=
  (profileInnerBlocks q N a t).image (profileMarkedDepth A q N)
/-- The fixed minimizing marked split point of the actual inner interval. -/
def profileSplitPoint (A : ℕ → ℝ) (q N a t : ℕ) : ℕ :=
  finiteProfileMinimizer A (profileSplitCandidates A q N a t)
end FalconerThetaGauge
