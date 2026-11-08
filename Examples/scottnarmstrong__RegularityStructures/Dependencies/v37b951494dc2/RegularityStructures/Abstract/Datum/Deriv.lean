/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Partial derivatives on the open half space `{t > 0}` of space-time

For a function `F` on `ℝ × ℝ³`, smooth on `{t > 0}`, the coordinate derivatives
`pd i F` (`i = 0` is time) are *total* functions, set to `0` for `t ≤ 0`, so that identities between
them hold as equalities of functions. `pdIter i n` is the `n`-fold derivative and
`D k = ∂₀^{k₀} ∂₁^{k₁} ∂₂^{k₂} ∂₃^{k₃}` for a multi-index `k` (time derivative outermost).

* `SmoothPos F`: `F` is `C^∞` on `{t > 0}`; it is stable under `pd`;
* `pd_comm`: mixed partials commute on `SmoothPos` functions;
* `D_add`: `D (m + l) F = D m (D l F)`.
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace RegularityStructures.Datum
/-- The open half space `{t > 0}` of space-time. -/
def posTime : Set ParabolicSpace := {z | 0 < z.1}
/-- The point of space-time with coordinates `c = (c₀, c₁, c₂, c₃)`. -/
def stOfCoords (c : Fin 4 → ℝ) : ParabolicSpace := (c 0, fun j => c j.succ)
/-- The `i`-th coordinate vector of space-time. -/
def stBasis (i : Fin 4) : ParabolicSpace := stOfCoords (Pi.single i 1)
/-- `F` is `C^∞` on the open half space `{t > 0}`. -/
def SmoothPos (F : ParabolicSpace → ℝ) : Prop := ContDiffOn ℝ ∞ F posTime
/-- The derivative of `F` in the direction `v`, for `t > 0` (and `0` for `t ≤ 0`). -/
def pdv (v : ParabolicSpace) (F : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  if 0 < z.1 then fderiv ℝ F z v else 0
/-- The partial derivative in the `i`-th coordinate direction. -/
def pd (i : Fin 4) : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ := pdv (stBasis i)
end RegularityStructures.Datum
end
public section
open scoped ContDiff
namespace RegularityStructures.Datum
theorem isOpen_posTime : IsOpen posTime :=
  isOpen_lt continuous_const continuous_fst
theorem pdv_of_pos {v : ParabolicSpace} {F : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hz : 0 < z.1) : pdv v F z = fderiv ℝ F z v := by
  simp [pdv, hz]
theorem SmoothPos.pdv {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (v : ParabolicSpace) :
    SmoothPos (pdv v F) := by
  have h : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) posTime :=
    (hF.fderiv_of_isOpen isOpen_posTime (by simp)).clm_apply contDiffOn_const
  exact h.congr fun z hz => pdv_of_pos hz
theorem SmoothPos.pd {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (i : Fin 4) :
    SmoothPos (pd i F) := hF.pdv _
theorem SmoothPos.smul {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ) :
    SmoothPos (c • F) := ContDiffOn.const_smul c hF
end RegularityStructures.Datum
end
