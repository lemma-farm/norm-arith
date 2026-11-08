/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.Semigroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section
/-!
# The generator relation of a strongly continuous semigroup

The generator is characterized by a right derivative in the ambient Banach norm. The semigroup
law propagates this derivative along each orbit. Integrating the right derivative gives the
usual integral identity and, in turn, two-sided differentiability at positive times.
These facts connect the explicit longitudinal heat construction to the operator in the paper.
-/
open Filter MeasureTheory Set Topology
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
/-- The orbit on real time, extended constantly to negative times. -/
def realOrbit (S : C0Semigroup ℂ E) (x : E) (t : ℝ) : E := S t.toNNReal x
def HasGeneratorAt (S : C0Semigroup ℂ E) (x y : E) : Prop :=
  HasDerivWithinAt (S.realOrbit x) y (Ici 0) 0
theorem HasGeneratorAt.apply {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (t : NNReal) : S.HasGeneratorAt (S t x) (S t y) := by
  have hd := ((S t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 h
  have heq : (fun s : ℝ ↦ S t (S.realOrbit x s)) = S.realOrbit (S t x) := by
    funext s
    simp only [realOrbit, ← S.add_apply, add_comm]
  change HasDerivWithinAt (fun s : ℝ ↦ S t (S.realOrbit x s)) (S t y) (Ici 0) 0 at hd
  rw [heq] at hd
  exact hd
end
end C0Semigroup
