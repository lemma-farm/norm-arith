module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Atomic.BesselSynthesis
public import Mathlib
import all Mathlib.Algebra.Order.BigOperators.Ring.Finset
@[expose] public section
/-!
# Finite Gram-form Schur bounds

This module connects pointwise localization of a Hermitian Gram kernel to the
finite quadratic estimate needed by `BesselAnalysis.of_finsupp_gram_bound`.
The scalar lemma is deliberately finite: no infinite matrix or bounded
operator is assumed before the row estimate has been proved.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped BigOperators
variable {ι H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
end
end MeyerGeneralProblem
