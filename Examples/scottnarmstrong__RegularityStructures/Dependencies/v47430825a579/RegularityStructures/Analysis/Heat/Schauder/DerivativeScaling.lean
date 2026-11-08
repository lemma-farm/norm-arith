/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Schauder.Shell
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scaling of derivatives of dyadic rescalings

For `h` smooth and supported in the unit parabolic ball and a multi-index `k`:
`D^k (scaledShell h n) = (2^n)^{|k|_𝔰} · scaledShell (D^k h) n` (`lineIter_multiDirs_scaledShell`),
and the `L¹` norms of `scaledShell F n` and of its generator scale exactly
(`integral_abs_scaledShell`, `integral_abs_parabolicGenerator_scaledShell`).
-/
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
