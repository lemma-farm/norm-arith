import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.V7.PositiveModel
namespace V7
inductive ObservableGuardKind where
  | upperModel | gradient | cocoercivity | interpolation | terminalDescent
  deriving DecidableEq
structure ObservableGuardFailure (d : ℕ) where
  kind : ObservableGuardKind
  x : Point d
  y : Point d
end V7
