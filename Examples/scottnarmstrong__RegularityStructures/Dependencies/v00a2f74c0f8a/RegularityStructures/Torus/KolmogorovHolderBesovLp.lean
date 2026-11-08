/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.KolmogorovHolderBesovHeat
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.PDE.Semigroup
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Heat-kernel Hölder bounds on the torus

This file proves the (L^p)-to-(L^\infty) estimate used in the dyadic Kolmogorov
argument.  The pointwise heat-kernel majorant is the periodised Gaussian estimate in
`KolmogorovHolderBesovHeat`; the normalization is the one in Hairer [Hai14, (2.1)--(2.3)].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
open PDE
end RegularityStructures
end
