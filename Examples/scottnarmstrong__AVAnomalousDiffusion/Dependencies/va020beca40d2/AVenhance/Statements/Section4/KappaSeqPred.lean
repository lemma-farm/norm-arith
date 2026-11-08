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
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section4.KappaSeq
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
variable {β : ℝ} (I : Ingredients β)
/-- `K̄_m^{κ_m} = κ_{m-1}` (source 3897-3898: "Recall `Khom_m^{κ_m} = κ_{m-1}` by
`e.kappa.sequence`"). -/
theorem kappaSeq_pred (κ : ℝ) {M m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    I.kappaSeq κ M (m - 1) = I.KhomScalar (I.kappaSeq κ M m) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : M - n = (M - (n + 1)) + 1 := by omega
  simp only [kappaSeq, Nat.add_sub_cancel]
  rw [h]
  rfl
end Ingredients
end AVenhance
