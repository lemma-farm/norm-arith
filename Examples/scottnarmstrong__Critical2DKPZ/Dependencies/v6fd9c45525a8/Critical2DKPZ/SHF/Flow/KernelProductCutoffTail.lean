/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Blocks.ArrivalKernel
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.PolymerCalculus.KernelReversal
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.SlabProductsCore
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.TerminalRandomWeightAnnealing
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.KernelProductCutoffBound
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.CutoffTailMoments
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.SlabSmoothedConnector
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Positivity.HeatClockBounds
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Limit.SubseqLimit
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Annealed cutoff tails for separated polymer blocks -/
@[expose] public section
open MeasureTheory
open scoped BigOperators CompactlySupported
namespace Critical2DKPZ.SHF.Flow
open Critical2DKPZ.Blocks
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
end Critical2DKPZ.SHF.Flow
end
