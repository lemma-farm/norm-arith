module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.ve2c706b4ba90.HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # C² homogeneous functions and their continuous Bellman images -/
@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The open punctured product plane. -/
def bellmanPuncturedSet : Set (ℝ × ℝ) := {q | q ≠ (0, 0)}
end HypoellipticAleksandrov.KineticAleksandrov
