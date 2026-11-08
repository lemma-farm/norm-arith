import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.V7.Guards
namespace V7
structure ObservableGuardCheck (d : ℕ) where
  kind : ObservableGuardKind
  xPair : Observation d
  yPair : Observation d
inductive TrialOutcome (d : ℕ) where
  | success (terminalPair : Observation d)
  | scale (failedCheck : ObservableGuardCheck d)
  | radius (terminalPair : Observation d)
/-- Observable data only: no `M<L` or `D<R` conclusion is stored here. -/
structure TrialReport (d : ℕ) where
  trace : List (Observation d)
  checkedGuards : List (ObservableGuardCheck d)
  outcome : TrialOutcome d
structure CachedPair (d : ℕ) where
  observation : Observation d
inductive LocalTrialAction (d : ℕ) (State : Type) where
  | query (point : Point d) (next : Observation d → State)
  | finish (guards : List (ObservableGuardCheck d)) (outcome : TrialOutcome d)
/-- A causal local trial: cached data enters the initial state, and all later
objective information enters only through `query` continuations. -/
structure LocalTrial (d : ℕ) where
  State : Type
  initial : ℝ → ℝ → CachedPair d → State
  action : State → LocalTrialAction d State
def LocalTrial.runFuel (trial : LocalTrial d) (oracle : PairOracle d) :
    ℕ → trial.State → List (Observation d) → Option (TrialReport d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match trial.action state with
      | .finish guards outcome => some ⟨history, guards, outcome⟩
      | .query x next =>
          let obs := oracle.observe x
          trial.runFuel oracle fuel (next obs) (history ++ [obs])
end V7
