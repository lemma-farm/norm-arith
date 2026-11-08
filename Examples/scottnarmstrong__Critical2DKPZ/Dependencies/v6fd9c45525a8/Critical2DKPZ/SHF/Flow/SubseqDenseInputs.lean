/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.SubseqBlockIndependence
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Limit.Basic
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Tsai.Cutoff
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Tsai.Defs
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Moment and approximate-composition conditions for polymer limits

These conditions specify compact-test moment convergence, sixth-moment bounds, cutoff tails, and approximate composition. -/
@[expose] public section
open MeasureTheory Filter
open scoped CompactlySupported Topology
namespace Critical2DKPZ.SHF.Flow
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
end Critical2DKPZ.SHF.Flow
end
