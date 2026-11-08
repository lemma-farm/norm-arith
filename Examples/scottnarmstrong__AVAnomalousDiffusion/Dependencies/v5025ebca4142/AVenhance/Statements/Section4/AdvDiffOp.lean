-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Construction.IsStreamSeq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Construction.StreamVelContinuous
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Construction.StreamVelLipschitz
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.FlowDefs.FlowInv
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.KappaAt
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.PermittedInterval
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.PermissibleSet
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.ChiM
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.Flux
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.TimeAvgMat
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.GradMatrix
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section3.SpaceLap
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.Ingredients
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.HatXiML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.HatZetaML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.XiMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.ZetaMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Infra.Ingredients.LIdxConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Infra.Cutoff.TimeScaleFacts
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Section4.VecDiv
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
/-- `(∂_t - κ Δ + b · ∇) u`, classical derivatives (source order of `e.theta.m`, label 3856). -/
def advDiffOp (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => u s x) t - κ * spaceLap (u t) x + vecDot (b t x) (spaceGrad (u t) x)
end AVenhance
