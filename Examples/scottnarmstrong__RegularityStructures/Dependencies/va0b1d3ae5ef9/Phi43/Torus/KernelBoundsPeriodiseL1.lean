/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.Torus.KernelBoundsL1
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.Torus.KernelBoundsMollifier
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.RegularityStructures.Torus.HeatKernelIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.ClassicalSolution.Periodise
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Fundamental-domain control of the periodised mollifier

The spatial periodisation does not increase the total variation: its `L¹` norm on the torus is
bounded by the `L¹` norm of the Euclidean lift.  The proof uses the half-open fundamental domain
and the finite lattice representation of the compactly supported rescaling.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set Submodule
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
