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
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Construction.StreamVelLipschitz
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
/-- The `k`-th term of `e.psi.recursion`, second form (1436-1455):
`ζ̂_{m,l_k}(t) ζ_{m,k}(t) ψ_{m,k}(X⁻¹_{m-1}(t, x, l_k τ''_m))`, where `X_{m-1}` is the
`flow` of the velocity `∇^⊥ φ_{m-1}` (admissibility of `φ_{m-1}` supplies the flow hypotheses). -/
def nextStreamTerm (m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (t : ℝ) (x : Vec 2) (k : ℤ) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
    psi β I.Λ m k
      (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
        ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m))
end Ingredients
end AVenhance
