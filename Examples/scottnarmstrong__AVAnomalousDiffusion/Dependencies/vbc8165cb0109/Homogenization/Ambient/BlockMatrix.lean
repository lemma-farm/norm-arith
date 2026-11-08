-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.Homogenization.Ambient.Basic
public import Mathlib
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)
/-- File-level typeclass cache for `Nonempty (BlockCoord d)`. -/
private instance instNonemptyBlockCoord (d : ℕ) [NeZero d] :
    Nonempty (BlockCoord d) := inferInstance
def MatLoewnerLE {d : ℕ} (A B : Mat d) : Prop :=
  ∀ x : Vec d,
    (1 / 2 : ℝ) * vecDot x (matVecMul A x) ≤
      (1 / 2 : ℝ) * vecDot x (matVecMul B x)
/--
Löwner order on doubled block matrices, expressed through the quadratic form
`\frac12 X \cdot \mathbf A X`.
-/
def BlockMatLoewnerLE {d : ℕ} (A B : BlockMat d) : Prop :=
  ∀ X : BlockVec d,
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X)
theorem MatLoewnerLE.trans {d : ℕ} {A B C : Mat d}
    (hAB : MatLoewnerLE A B) (hBC : MatLoewnerLE B C) :
    MatLoewnerLE A C := by
  intro x
  exact le_trans (hAB x) (hBC x)
theorem BlockMatLoewnerLE.trans {d : ℕ} {A B C : BlockMat d}
    (hAB : BlockMatLoewnerLE A B) (hBC : BlockMatLoewnerLE B C) :
    BlockMatLoewnerLE A C := by
  intro X
  exact le_trans (hAB X) (hBC X)
end Homogenization
