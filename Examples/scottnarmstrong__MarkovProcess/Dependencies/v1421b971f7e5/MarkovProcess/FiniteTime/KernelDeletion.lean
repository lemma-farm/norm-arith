/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.KernelShift
import Mathlib.Probability.Kernel.Composition.KernelLemmas
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Deleting one coordinate from a finite-time kernel

For a conservative sub-Markov kernel semigroup, removing one observation from a finite-time law
gives the law on the remaining ordered times.  This is finite-dimensional kernel infrastructure;
it does not construct a path-space law or a stochastic process.
-/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
