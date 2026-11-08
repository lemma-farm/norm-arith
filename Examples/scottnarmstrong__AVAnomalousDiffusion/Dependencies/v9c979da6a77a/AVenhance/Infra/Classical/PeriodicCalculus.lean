-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.Drift
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.Calculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Real-valued periodic integration by parts on the unit cell. -/
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open Set
open AVenhance.Infra.Torus
namespace AVenhance.Infra.Classical
theorem periodic_spaceGrad_component {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i) := by
  intro n x
  let a := AVenhance.latticeShift n
  have hEq : (fun y => f (y + a)) = f := by
    funext y
    exact hper n y
  have hderiv : fderiv ℝ f (x + a) = fderiv ℝ f x := by
    calc
      fderiv ℝ f (x + a) = fderiv ℝ (fun y => f (y + a)) x := by
        rw [fderiv_comp_add_right]
      _ = fderiv ℝ f x := by rw [hEq]
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i)) hderiv
end AVenhance.Infra.Classical
end
