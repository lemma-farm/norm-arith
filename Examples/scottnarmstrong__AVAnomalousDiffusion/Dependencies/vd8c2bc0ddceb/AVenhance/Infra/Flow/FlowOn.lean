-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.AVenhance.Statements.Flow.IsFlow
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! A global-flow interface for normed state spaces beyond the case `Vec 2`. -/
@[expose] public section
namespace AVenhance.Infra.Flow
/-- A characterized global ODE flow on an arbitrary normed state space. -/
def IsFlowOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → E) (Y : ℝ → E → ℝ → E) : Prop :=
  (∀ y s, Y s y s = y) ∧
  (∀ y s t, HasDerivAt (fun r => Y r y s) (F t (Y t y s)) t)
end AVenhance.Infra.Flow
