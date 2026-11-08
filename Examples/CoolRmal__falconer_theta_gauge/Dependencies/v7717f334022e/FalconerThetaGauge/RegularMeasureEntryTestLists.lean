/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureEntryTests
public import Mathlib
set_option autoImplicit false
/-!
# Actual scheduled test lists and their origins

The list of an interval is the actual finite union over all its long
subintervals. Its tests retain real origins, the lists increase with interval
inclusion, and their exact cardinality is bounded by `N²` at the parameters
of the manuscript.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
/-- The actual long subintervals contributing tests to `[a,t]`. -/
def profileScheduleOrigins (q a t : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc a t).product (Finset.Icc a t)).filter (fun r ↦ 100 * q < r.2 - r.1)
/-- The actual list `T([a,t])`, as a finite set of concrete tube and projection tests. -/
def profileScheduledTests (A : ℕ → ℝ) (q N a t : ℕ) : Finset ProfileScheduleTest :=
  (profileScheduleOrigins q a t).biUnion (fun r ↦ profileContributedTests A q N r.1 r.2)
end FalconerThetaGauge
