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
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.memSobolevX
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.sobolevXENorm
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
def memSobolevXZero {m n : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  memSobolevX w X V k p f ∧
  ∃ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞),
    Tendsto (fun j => sobolevXENorm w X V k p (fun x => f x - φ j x))
      atTop (𝓝 0)
end RothschildStein
