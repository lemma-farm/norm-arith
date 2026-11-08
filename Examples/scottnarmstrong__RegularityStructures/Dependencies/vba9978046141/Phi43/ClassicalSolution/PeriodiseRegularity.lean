/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.ClassicalSolution.Periodise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Regularity of the periodised mollifier

The compact support of a mollifier makes its spatial lattice sum locally finite.  We first prove
this as a statement about a function on `ℝ × ℝ³`; the periodic lift of `periodise` is then a
locally finite sum of smooth functions.  The support and boundedness statements are the analytic
facts used for the mollified covariance (item (W3) of Lemma 4.1 of the statement).
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
open scoped Topology
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
