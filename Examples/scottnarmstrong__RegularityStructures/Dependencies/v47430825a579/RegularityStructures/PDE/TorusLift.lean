/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.UniformSpace.HeineCantor
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Lifting functions between `T³` and `ℝ³`

The projection `torusProj : ℝ³ → T³` is a continuous additive open quotient map that does not
increase distances. A continuous function on `ℝ³` that is constant on the fibres of `torusProj`
descends to a continuous function on `T³` (`torusDescend`). Derivatives of functions on `T³` are
those of their periodic lifts (`HasTorusDeriv`). Finally `torusShift a` is the translation
`g ↦ g(· + a)` on `C(T³, E)`, as a continuous linear map.

These are the bookkeeping tools of the semilinear heat theory in `RegularityStructures/PDE/`.
-/
@[expose] public noncomputable section
open Set
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
public section
open Set Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-! ### The projection `ℝ³ → T³` -/
theorem torusProj_add (a b : Fin 3 → ℝ) : torusProj (a + b) = torusProj a + torusProj b := by
  funext i
  simp [torusProj]
theorem torusProj_zero : torusProj 0 = 0 := by
  funext i
  simp [torusProj]
theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
theorem torusProj_torusRep (x : Torus3) : torusProj (torusRep x) = x := by
  funext i
  simp [torusProj, torusRep]
end RegularityStructures.PDE
end
