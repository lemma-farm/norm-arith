module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.FiniteChainPruning
public import Mathlib
public import Mathlib.Tactic
public section
noncomputable section
open scoped Classical
namespace SKConstants
namespace Cheeger
variable {V : Type*} [Fintype V] [DecidableEq V]
@[expose] def indicator (S : Finset V) (x : V) : ℝ := if x ∈ S then 1 else 0
end Cheeger
end SKConstants
