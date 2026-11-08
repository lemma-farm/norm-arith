-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Construction.IsStreamSeq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Construction.StreamVelContinuous
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Construction.StreamVelLipschitz
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.FlowDefs.FlowInv
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.KappaAt
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.PermittedInterval
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.PermissibleSet
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.ChiM
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.Flux
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.TimeAvgMat
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.GradMatrix
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.SpaceLap
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.Ingredients
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.HatXiML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.HatZetaML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.XiMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.ZetaMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Ingredients.LIdxConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Cutoff.TimeScaleFacts
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section4.XFlowInv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Public statement. -/
@[expose] public section
open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
/-- `∇X_{m-1,l} ∘ X⁻¹_{m-1,l}` (`e.sm`, `e.chainrule.Tm1`): the matrix whose `(i,j)` entry is
`∂_i X^j_{m-1,l}` evaluated at `X⁻¹_{m-1,l}(t,x)`; row vectors for vector-valued functions and
column vectors for gradients, exactly the convention of `e.gradcorrmatrix` (`gradMatrix`), so
`∇(T∘X_l)∘X_l⁻¹ = (∇X_l∘X_l⁻¹) ∇T`. -/
def flowGrad (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gradMatrix (fun y => I.xFlow hΦ m l t y) (I.xFlowInv hΦ m l t x)
end Ingredients
end AVenhance
