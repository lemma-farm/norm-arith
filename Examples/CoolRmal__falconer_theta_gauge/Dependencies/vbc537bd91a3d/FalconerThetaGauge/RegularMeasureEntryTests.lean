/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntryScheduleGains
public import Mathlib
set_option autoImplicit false
/-!
# Actual tube and projection tests contributed by one interval

Each concrete test records its kind, anchor and other endpoint. The origin
contains its symmetric length interval and contributes every shorter tube
test with the same anchor.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
/-- The two test types in the manuscript. -/
inductive ProfileTestKind
  | tube
  | projection
  deriving DecidableEq
instance : Fintype ProfileTestKind where
  elems := {.tube, .projection}
  complete := by intro k; cases k <;> simp
/-- A concrete finite-depth test with its anchor and other endpoint. -/
structure ProfileScheduleTest where
  kind : ProfileTestKind
  anchor : ℕ
  endpoint : ℕ
  deriving DecidableEq
/-- The length of a tube `[g,p]` or projection `[p,u]` test. -/
def ProfileScheduleTest.length (test : ProfileScheduleTest) : ℕ :=
  match test.kind with
  | .tube => test.anchor - test.endpoint
  | .projection => test.endpoint - test.anchor
/-- The concrete tube tests and possible projection test contributed by one split. -/
def profileTestsAtSplit (a p t : ℕ) : Finset ProfileScheduleTest :=
  ((Finset.Ico (p - min (p - a) (t - p)) p).image
    (fun g ↦ (⟨.tube, p, g⟩ : ProfileScheduleTest))) ∪
      if a + t < 2 * p then {⟨.projection, p, t⟩} else ∅
/-- The tests actually contributed by an interval, using its constructed split point. -/
def profileContributedTests (A : ℕ → ℝ) (q N a t : ℕ) : Finset ProfileScheduleTest :=
  profileTestsAtSplit a (profileSplitPoint A q N a t) t
end FalconerThetaGauge
