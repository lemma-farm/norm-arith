/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.RegularityStructures.Torus.KernelBoundsGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Large-time bounds for the massive torus heat kernel

The periodised Gaussian has a uniformly bounded spatial profile once `t ≥ 1`.  The proof uses
the one-dimensional Jacobi transformation, followed by factorisation over the three coordinates.
This is the large-scale part of [Hai14, Assumption 5.1, (5.3)] (arXiv:1303.5113v4).
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
namespace RegularityStructures
end RegularityStructures
end
