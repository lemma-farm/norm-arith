import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.O3.Foundation
/-!
# Exact pair-oracle observations and guarded trial reports

This module contains data only: exact oracle observations, finite traces,
observable scalar guard checks, and the three possible trial outcomes.  In
particular, a `TrialReport` does not contain a proof of a target gradient
bound, a radius classification, or successful controller termination.
Those properties live in the separate proposition `TrialValid` and must be
proved by the regime-specific trial modules.
-/
namespace O3
/-- A finite, chronological list of counted pair-oracle observations. -/
abbrev OracleTrace (d : ℕ) := List (Observation d)
inductive GuardKind where
  | upperModel
  | gradientLipschitz
  | interpolation
  deriving DecidableEq
/--
An observable guard is stored through its scalar margin.  The convention is
that the checked inequality passes exactly when `0 ≤ margin`.
-/
structure GuardCheck where
  kind : GuardKind
  margin : ℝ
inductive TrialOutcome (d : ℕ) where
  | success (point : Vec d)
  | scale (failedKind : GuardKind)
  | radius (finalPoint : Vec d)
/--
Finite data emitted by a local trial.  `calls` is deliberately not a free
field: it is the length of the exact observation trace.
-/
structure TrialReport (d : ℕ) where
  observations : OracleTrace d
  guards : List GuardCheck
  outcome : TrialOutcome d
inductive TrialMachineAction (d : ℕ) (State : Type) where
  | query (point : Vec d) (next : Observation d → State)
  | finish (guards : List GuardCheck) (outcome : TrialOutcome d)
/-- A deterministic guarded-trial state-machine component, parameterized by `M,D`. -/
structure GuardedTrialMachine (d : ℕ) where
  State : Type
  initial : ℝ → ℝ → State
  action : State → TrialMachineAction d State
/--
Fuel-bounded execution of a local trial.  The returned report contains exactly
the chronological calls performed by its `query` transitions.
-/
def GuardedTrialMachine.runFuel {d : ℕ} (machine : GuardedTrialMachine d)
    (oracle : PairOracle d) :
    ℕ → machine.State → OracleTrace d → Option (TrialReport d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match machine.action state with
      | .finish guards outcome => some ⟨history, guards, outcome⟩
      | .query x next =>
          let obs := oracle.observe x
          machine.runFuel oracle fuel (next obs) (history ++ [obs])
def GuardedTrialMachine.run {d : ℕ} (machine : GuardedTrialMachine d)
    (oracle : PairOracle d) (M D : ℝ) (fuel : ℕ) : Option (TrialReport d) :=
  machine.runFuel oracle fuel (machine.initial M D) []
end O3
