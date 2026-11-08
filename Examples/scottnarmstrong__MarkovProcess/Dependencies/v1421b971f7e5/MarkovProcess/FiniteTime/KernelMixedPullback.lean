/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.KernelConcatenation
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Pulling a finite-time concatenation back to mixed labels

This file records the reindexing step after an ordered finite-dimensional law has been split at
a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
terminal past label without requiring either label to be present.

The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
continuity, density, path-space, or Feller hypothesis.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]
namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
