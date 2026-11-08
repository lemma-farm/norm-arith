/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.DenseFiltration
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.DenseTimeFiniteShift
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.PhysicalReindex
import Mathlib.Data.Finset.Sum
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.KernelMixedPullback
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/
namespace MarkovProcess
section MixedPastFutureCoordinates
open MeasureTheory
noncomputable section
namespace MixedPastFuture
variable {alpha : Type*} [MeasurableSpace alpha]
end MixedPastFuture
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
variable [MeasurableSpace alpha] [BorelSpace alpha]
end ContinuousPath
namespace ContinuousPath
variable {alpha : Type*} [PseudoMetricSpace alpha]
end ContinuousPath
end
end MixedPastFutureCoordinates
section MixedPastFutureCutCoordinates
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace MixedPastFuture
noncomputable section
variable {alpha : Type*}
variable [MeasurableSpace alpha]
end
end MixedPastFuture
namespace SubMarkovKernelSemigroup
namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MixedPastFutureCutCoordinates
section MixedPastFutureCutFactorization
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace SubMarkovKernelSemigroup
namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MixedPastFutureCutFactorization
end MarkovProcess
