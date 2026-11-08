-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.FlowDefs.FlowInv
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.SigmaMat
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.HatZetaML
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.ZetaMK
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.Psi
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Ingredients.LIdx
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.IsHolderClass
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.IsDivFree
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Flow.SmoothField
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Construction.BarNorm
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
/-- Admissible stream functions of the construction (source 1398-1414, 1457-1461): `C^∞`
in `(t,x)` and `ℤ × ℤ²`-periodic (`φ (t + n) (x + k) = φ t x`). The normalization
`⟨φ_m⟩ = 0` of `e.phim.bm` is deliberately not part of admissibility (see proposal). -/
def IsAdmissibleStream (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ) ∧
  ∀ (n : ℤ) (k : Fin 2 → ℤ) (t : ℝ) (x : Vec 2),
    φ (t + (n : ℝ)) (x + latticeShift k) = φ t x
end AVenhance
