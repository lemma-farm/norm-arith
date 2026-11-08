module
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.Ambient.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moving-fiber kernels

This module fixes the carrier for the terminal evolution kernel.  Invalid
time pairs and off-domain source states have no values: the master kernel is
defined only on the corresponding valid-query subtype.  Fixed-time kernels
are obtained from that one master kernel by `Kernel.comap` and
`Kernel.comapRight`.
-/
@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ProbabilityTheory
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The ambient fixed-time state `(y, z)`. -/
abbrev EvolutionAmbientState (n : ℕ) := PDE.Vec n × PDE.Vec n
/-- The moving spatial domain obtained by translating the base domain. -/
def movingDomain {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    Set (PDE.Vec n) :=
  PDE.translateSet (γ σ) Ω
/-- The open ambient state fiber at a fixed time. -/
def evolutionStateSet {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) : Set (EvolutionAmbientState n) :=
  movingDomain Ω γ σ ×ˢ Set.univ
abbrev RawEvolutionQuery (n : ℕ) :=
  ℝ × (ℝ × EvolutionAmbientState n)
/-- A query with valid time order and a source state in the moving fiber. -/
abbrev EvolutionQuery {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) :=
  {q : RawEvolutionQuery n //
    q.1 ≤ q.2.1 ∧ q.2.2 ∈ evolutionStateSet Ω γ q.1}
structure MovingFiberKernel {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) where
  master : ProbabilityTheory.Kernel
    (EvolutionQuery Ω γ) (EvolutionAmbientState n)
  /-- Every master output is supported on the open terminal state fiber. -/
  terminal_support : ∀ q : EvolutionQuery Ω γ,
    (master q).restrict (evolutionStateSet Ω γ q.1.2.1) = master q
  /-- The master kernel has sub-Markov mass. -/
  mass_le_one : ∀ q : EvolutionQuery Ω γ, master q Set.univ ≤ 1
namespace MovingFiberKernel
end MovingFiberKernel
namespace MovingFiberKernel
end MovingFiberKernel
end HypoellipticAleksandrov.KineticAleksandrov
