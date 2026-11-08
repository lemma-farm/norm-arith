module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.CoarseDeGiorgi.NegSobolev.GaussDerivPolynomial
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.CoarseDeGiorgi.NegSobolev.GaussDerivLp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! A wider Gaussian dominates each fixed order of Gaussian derivatives. -/
@[expose] public section
open Homogenization MeasureTheory Polynomial Filter
open scoped BigOperators Topology
namespace CoarseDeGiorgi.NegSobolev
end CoarseDeGiorgi.NegSobolev
