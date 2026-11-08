/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.KernelRestriction
import Mathlib.Probability.Kernel.Composition.Lemmas
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace MarkovProcess
namespace FiniteOrderedTimes
end FiniteOrderedTimes
namespace SubMarkovKernelSemigroup
variable {alpha : Type*} [MeasurableSpace alpha]
namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
