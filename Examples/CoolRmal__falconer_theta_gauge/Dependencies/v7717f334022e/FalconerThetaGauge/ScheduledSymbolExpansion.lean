module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ScheduledSymbolOneStep
public import Mathlib
set_option autoImplicit false
/-! # Literal finite differentiation trees and the exact coefficient budget in S3 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical ContDiff
namespace FalconerThetaGauge
/-- A branch records exactly which listed mask was differentiated at each step. -/
def ScheduledSymbolBranch (I : Finset ProfileScheduleTest) : ℕ → Type
  | 0 => Unit
  | j + 1 => ScheduledSymbolBranch I j × {test // test ∈ I}
instance scheduledSymbolBranchFintype (I : Finset ProfileScheduleTest) (j : ℕ) :
    Fintype (ScheduledSymbolBranch I j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ j ih =>
    change Fintype (ScheduledSymbolBranch I j × {test // test ∈ I})
    letI := ih
    infer_instance
end FalconerThetaGauge
