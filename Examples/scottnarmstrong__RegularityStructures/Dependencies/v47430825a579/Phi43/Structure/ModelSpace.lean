/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Structure.Symbols
public import Mathlib.Data.Finsupp.Single
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The finite graded model space and structure group

The model space is the free real vector space on the finite symbol sector.  Its
product is the linear extension of the product table in `Phi43.Structure.Symbols`, with
unlisted products set to zero as in Hairer's construction after (8.4).

The structure-group action is defined on the primitive generators and on the
Taylor products by multiplication in this algebra.  Thus the formulas for
`XᵢΨ`, `XᵢXⱼ`, `XᵢΨ²`, and the products entering `U³` are derived from the
generator action; they are not an independently listed action table.  The
non-trivial parameter cocycle is the spatial Taylor term in the action of
`I(Ψ)Ψ` and `I(Ψ)Ψ²`.
-/
@[expose] public noncomputable section
namespace RegularityStructures.Phi43
open scoped BigOperators
/-- The free model space on the finite symbol basis. -/
abbrev T : Type := Symbol →₀ ℝ
/-- The basis vector associated with a symbol. -/
def basis (τ : Symbol) : T := Finsupp.single τ 1
/-- The bilinear basis product, with absent finite products equal to zero. -/
def basisProduct (a b : Symbol) : T :=
  match productSymbol a b with
  | some c => basis c
  | none => 0
/-- The bilinear product on `T`, obtained by linear extension of `basisProduct`. -/
def basisProductLinear (a : Symbol) : T →ₗ[ℝ] T :=
  Finsupp.linearCombination ℝ (fun b => basisProduct a b)
def multiply (v w : T) : T :=
  Finsupp.linearCombination ℝ (fun a => basisProductLinear a w) v
instance mulT : Mul T := ⟨multiply⟩
@[simp]
theorem basisProduct_eq (a b : Symbol) : basisProduct a b =
    match productSymbol a b with
    | some c => basis c
    | none => 0 := by
  rfl
@[simp]
theorem multiply_basis (a b : Symbol) : basis a * basis b = basisProduct a b := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (basis b))
    (Finsupp.single a 1) = basisProduct a b
  rw [Finsupp.linearCombination_single]
  simp [basisProductLinear, basis]
@[simp]
theorem multiply_zero_left (v : T) : 0 * v = 0 := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a v) 0 = 0
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a v)).map_zero
theorem multiply_add_left (v w z : T) : (v + w) * z = v * z + w * z := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a z) (v + w) = _
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a z)).map_add v w
theorem multiply_add_right (v w z : T) : v * (w + z) = v * w + v * z := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw =>
      simp only [multiply_add_left, ihv, ihw, add_add_add_comm]
  | single a r =>
      change multiply (Finsupp.single a r) (w + z) =
        multiply (Finsupp.single a r) w + multiply (Finsupp.single a r) z
      change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (w + z))
          (Finsupp.single a r) =
        Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)
            (Finsupp.single a r) +
          Finsupp.linearCombination ℝ (fun a => basisProductLinear a z)
            (Finsupp.single a r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single]
      rw [(basisProductLinear a).map_add, smul_add]
theorem multiply_smul_left (r : ℝ) (v w : T) : (r • v) * w = r • (v * w) := by
  change Finsupp.linearCombination ℝ (fun a => basisProductLinear a w) (r • v) = _
  exact (Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)).map_smul r v
theorem multiply_smul_right (r : ℝ) (v w : T) : v * (r • w) = r • (v * w) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w ihv ihw =>
      simp only [multiply_add_left, ihv, ihw, smul_add]
  | single a s =>
      change multiply (Finsupp.single a s) (r • w) =
        r • multiply (Finsupp.single a s) w
      change Finsupp.linearCombination ℝ (fun a => basisProductLinear a (r • w))
          (Finsupp.single a s) =
        r • Finsupp.linearCombination ℝ (fun a => basisProductLinear a w)
          (Finsupp.single a s)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      rw [(basisProductLinear a).map_smul, smul_smul, smul_smul, mul_comm]
theorem multiply_neg_left (v w : T) : (-v) * w = -(v * w) := by
  rw [← neg_one_smul ℝ v, multiply_smul_left, neg_one_smul]
theorem multiply_neg_right (v w : T) : v * (-w) = -(v * w) := by
  rw [← neg_one_smul ℝ w, multiply_smul_right, neg_one_smul]
attribute [simp] multiply_add_left multiply_add_right multiply_smul_left multiply_smul_right
  multiply_neg_left multiply_neg_right
structure StructureParameters where
  shift : Fin 4 → ℝ
  cPsi : ℝ
  cPsiGrad : Fin 3 → ℝ
  cPsiSq : ℝ
  cPsiCube : ℝ
abbrev G := StructureParameters
instance : Zero StructureParameters :=
  ⟨0, 0, 0, 0, 0⟩
/-- Composition of structure-group parameters. -/
def structureGroupMul (g h : G) : G :=
  { shift := g.shift + h.shift
    cPsi := g.cPsi + h.cPsi + ∑ i : Fin 3, g.shift i.succ * h.cPsiGrad i
    cPsiGrad := g.cPsiGrad + h.cPsiGrad
    cPsiSq := g.cPsiSq + h.cPsiSq
    cPsiCube := g.cPsiCube + h.cPsiCube }
instance : Mul G := ⟨structureGroupMul⟩
end RegularityStructures.Phi43
end
