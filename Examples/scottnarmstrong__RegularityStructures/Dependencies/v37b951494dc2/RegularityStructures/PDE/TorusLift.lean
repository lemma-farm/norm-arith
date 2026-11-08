/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Torus.Basic
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
def ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E :=
  ∑ i : Fin 3, (ContinuousLinearMap.smulRightL ℝ (Fin 3 → ℝ) E
    (ContinuousLinearMap.proj i)).comp (ContinuousLinearMap.proj i)
/-- `g` has partial derivatives `Dg` on the torus: the periodic lift of `g` has Fréchet derivative
`k ↦ Σᵢ kᵢ Dg(y)ᵢ` at every `y ∈ ℝ³`. Derivatives are recorded through their partial derivatives,
so higher derivatives take values in iterated products `Fin 3 → Fin 3 → E`. -/
def HasTorusDeriv (g : C(Torus3, E)) (Dg : C(Torus3, Fin 3 → E)) : Prop :=
  ∀ y : Fin 3 → ℝ, HasFDerivAt (fun y => g (torusProj y)) (ofPartials (Dg (torusProj y))) y
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
theorem torusProj_neg (a : Fin 3 → ℝ) : torusProj (-a) = -torusProj a := by
  funext i
  simp [torusProj]
theorem torusProj_sub (a b : Fin 3 → ℝ) : torusProj (a - b) = torusProj a - torusProj b := by
  rw [sub_eq_add_neg, torusProj_add, torusProj_neg, ← sub_eq_add_neg]
@[fun_prop]
theorem continuous_torusProj : Continuous torusProj :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
theorem torusProj_torusRep (x : Torus3) : torusProj (torusRep x) = x := by
  funext i
  simp [torusProj, torusRep]
theorem torusProj_surjective : Function.Surjective torusProj :=
  fun x => ⟨torusRep x, torusProj_torusRep x⟩
theorem torusProj_eq_iff_sub (a b : Fin 3 → ℝ) :
    torusProj a = torusProj b ↔ torusProj (a - b) = 0 := by
  rw [torusProj_sub, sub_eq_zero]
end RegularityStructures.PDE
end
