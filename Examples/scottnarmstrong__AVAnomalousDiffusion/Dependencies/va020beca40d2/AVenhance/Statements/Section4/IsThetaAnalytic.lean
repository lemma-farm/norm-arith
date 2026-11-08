-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Construction.IsStreamSeq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Construction.StreamVelContinuous
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Construction.StreamVelLipschitz
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.FlowDefs.FlowInv
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.KappaAt
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.PermittedInterval
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.PermissibleSet
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.ChiM
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.Flux
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.TimeAvgMat
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.GradMatrix
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.SpaceLap
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Ingredients.Ingredients
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Ingredients.HatXiML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Ingredients.HatZetaML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Ingredients.XiMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Ingredients.ZetaMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Ingredients.LIdxConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Cutoff.TimeScaleFacts
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section4.HMinusOneNorm
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
/-- `e.theta0.anal` (3835-3838) = `e.theta0.anal.encore` (8030-8035): with `‖∇ⁿ f‖_X := max_{|α|=n}
‖∂^α f‖_X` (`e.nabla.n`, 944) the two displays coincide.  The maximum over multi-indices is
expressed as a bound for every ordered coordinate tuple `i : Fin n → Fin 2` (as in `barNorm`; equal
for `C^n` functions by symmetry of the derivative), for every `n ∈ ℕ = {1,2,…}`. -/
def IsThetaAnalytic (R : ℝ) (θ₀ : Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : Fin n → Fin 2,
    Real.sqrt (∫ x in unitCube, (iteratedFDeriv ℝ n θ₀ x (fun j => basisVec (i j))) ^ 2) ≤
      Real.sqrt (l2NormSq θ₀) * ((n.factorial : ℝ) / R ^ n)
end AVenhance
