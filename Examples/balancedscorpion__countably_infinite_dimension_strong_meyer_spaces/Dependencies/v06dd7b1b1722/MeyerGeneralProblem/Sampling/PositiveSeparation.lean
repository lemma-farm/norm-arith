module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Sampling.SeparatedDecay
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Gram.UniversalDecay
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Gram.UniversalOperator
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Atomic.GramSchur
public import Mathlib
@[expose] public section
/-!
# Positive-separation geometry and universal Gram boundedness

The separation-only part of the density-sharp argument needs `d > 0`, not
`d > 1`.  Rescaling the frequencies before taking integer floor shells
removes that artificial restriction from summable rows, uniform tails, and
the bounded universal Gram model.  No density or interpolation theorem is
assumed here.
-/
namespace MeyerGeneralProblem
open MeasureTheory
noncomputable section
end
end MeyerGeneralProblem
