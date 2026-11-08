/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.RegularityStructures.Torus.KernelBoundsGaussian
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Elementary geometry of the centered torus representative

These lemmas make the parabolic triangle estimate explicit.  The centered representative is used
only for the Euclidean spatial norm; all quotient identities are discharged in `AddCircle`.
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
theorem torusProj_torusCenteredRep (x : Torus3) :
    torusProj (torusCenteredRep x) = x := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  funext i
  dsimp [torusProj]
  have hrep : ((torusRep x i : ℝ) : UnitAddCircle) = x i := by
    dsimp [torusRep]
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
      (y := (x i : UnitAddCircle))
  rw [← hrep]
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-(m i), ?_⟩
  have hi := congrFun hm i
  rw [hi]
  simp only [zsmul_eq_mul, Pi.add_apply]
  rw [Int.cast_neg]
  ring
end RegularityStructures
end
