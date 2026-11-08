-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.fieldDerivative
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.fieldTranspose
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.wordTransposeTest
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.wordTranspose
public import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
end RothschildStein.S
