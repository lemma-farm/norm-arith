/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.KernelIdentification
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace Kernel
noncomputable section
variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]
variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
end
end Kernel
end MarkovProcess
