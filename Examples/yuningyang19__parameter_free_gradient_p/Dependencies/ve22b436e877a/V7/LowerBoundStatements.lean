import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.V7.AboveTwoStatements
import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.V7.StrictModel
open scoped BigOperators
namespace V7
/-- Causal deterministic exact-pair algorithm for the known-parameter lower
bound.  No inverse-gradient or unqueried-output channel is present. -/
structure DeterministicExactPairAlgorithm (d : ℕ) where
  nextQuery : Point d → List (Observation d) → Point d
  output : Point d → List (Observation d) → Point d
structure SmoothingKernelData (p : ℝ) (d : ℕ) where
  phi : Point d → ℝ
  gradPhi : Point d → Point d
  hessian : Point d → (Point d →L[ℝ] Point d)
  Mpd : ℝ
  smooth : ℝ → (Point d → ℝ) → PairOracle d
structure LowerCompletionData (p : ℝ) (d T : ℕ) where
  algorithm : DeterministicExactPairAlgorithm d
  x0 : Point d
  kernel : SmoothingKernelData p d
  Delta : ℝ
  delta : ℝ
  chi : ℝ
  beta : ℝ
  partialG : ℕ → Point d → ℝ
  partialH : ℕ → Point d → ℝ
  partialOracle : ℕ → PairOracle d
  completedOracle : PairOracle d
  queries : ℕ → Point d
  sigma : ℕ → Fin d
  xi : ℕ → ℝ
end V7
