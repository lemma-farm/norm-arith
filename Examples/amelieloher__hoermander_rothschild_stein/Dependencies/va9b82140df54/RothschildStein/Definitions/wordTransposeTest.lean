-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.Hormander.Interface.EuclideanDivergence
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.fieldTransposeTest
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
def wordTransposeTest {m n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) :
    List (Fin m) → TestFunction Ω ℝ (⊤ : ℕ∞) → TestFunction Ω ℝ (⊤ : ℕ∞)
  | [], φ => φ
  | i :: I, φ => wordTransposeTest Ω X hX I
      (fieldTransposeTest Ω (X i) (hX i) φ)
end RothschildStein
