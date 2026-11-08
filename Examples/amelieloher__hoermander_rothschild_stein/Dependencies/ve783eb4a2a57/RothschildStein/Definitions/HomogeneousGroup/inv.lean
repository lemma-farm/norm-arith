-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.BasisVec
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.HomogeneousGroup
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
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.inv {N : ℕ} (G : HomogeneousGroup N)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j => MvPolynomial.eval x (G.inversePolynomial j)
end RothschildStein
