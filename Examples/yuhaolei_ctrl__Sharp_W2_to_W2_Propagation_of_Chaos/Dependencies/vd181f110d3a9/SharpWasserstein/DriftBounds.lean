module
public import Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vd181f110d3a9.SharpWasserstein.Dynamics
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section
/-! Bounds on the actual interaction and McKean--Vlasov drifts. The constants
below are independent of the particle number. The coordinate-space norm in
this file is the ambient sup norm; quadratic-cost bounds are stated separately. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SharpWasserstein
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
end SharpWasserstein
