/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.RegularityStructures.Torus.KernelBoundsGlobal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.Phi43.Torus.KernelBoundsSupport
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.Phi43.Torus.KernelBoundsConvolution
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Uniform singular bound for the mollified massive heat kernel

The compact support of the periodised mollifier and the global singular majorant for the massive
heat kernel give the ε-uniform estimate for the mollified kernel.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
