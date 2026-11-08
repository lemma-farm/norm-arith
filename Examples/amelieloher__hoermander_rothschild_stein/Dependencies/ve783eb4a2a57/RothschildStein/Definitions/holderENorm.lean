-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.EuclideanDivergence
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.LieAlgebraSpansOn
public import Mathlib
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.holderSeminorm
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def holderENorm {n : ℕ}
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (α : ℝ) (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  (⨆ x : V, ENNReal.ofReal |f x|) + holderSeminorm d α V f
end RothschildStein
