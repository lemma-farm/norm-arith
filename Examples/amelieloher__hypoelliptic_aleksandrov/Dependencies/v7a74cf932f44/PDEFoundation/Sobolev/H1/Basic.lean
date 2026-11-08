module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Representative-level `H¹`

This file supplies the field-name-compatible `H1Function` interface used by
the application repositories. It is exactly the `p = 2` specialization of the
representative-level `W1pFunction` API: the explicit equivalence below loses
neither the chosen value representative nor the chosen gradient
representative.

The representative bundle is convenient for pointwise formulas. It is not the
complete Sobolev carrier; `PDEFoundation.Sobolev.H1.Graph` names the canonical
quotient graph.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
/-- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u
/-- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du
/-- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`.

This deliberately matches the established application-repository field names.
Use `H1Graph U` when completeness or quotient-level functional analysis is
required.
-/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad
instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun
namespace H1Function
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl
def toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient
end H1Function
namespace W1pFunction
/-- Regard a representative-level `W1pFunction` at `p = 2` as the exactly
corresponding `H1Function`. -/
def toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient
@[simp]
theorem toH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toFun = u.toFun :=
  rfl
@[simp]
theorem toH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.grad = u.grad :=
  rfl
end W1pFunction
namespace H1Function
def restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function
end H1Function
namespace W1pFunction
end W1pFunction
end PDE
