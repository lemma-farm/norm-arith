import Mathlib

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorDefs ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# The analytic tensors from Soberon's Theorem 2

This file defines the explicit tensors used in Section 3 of Soberon's v2
proof.  The elementary polarization identities are proved here.  The global nonvanishing statement remains in Tensors.lean. This module
contains only definitions and elementary proofs, so it can be checked separately.
-/
noncomputable section
namespace SoberonConvexBody
namespace Tensors
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
local notation "x₀(" x ")" => x (0 : Fin 4)
local notation "x₁(" x ")" => x (1 : Fin 4)
local notation "x₂(" x ")" => x (2 : Fin 4)
local notation "x₃(" x ")" => x (3 : Fin 4)
def IsONFrame (q : Fin 4 → E4) : Prop :=
  ∀ i j, inner ℝ (q i) (q j) = if i = j then 1 else 0

end Tensors
end SoberonConvexBody

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.FrameBasics ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
noncomputable section
namespace SoberonConvexBody
open scoped BigOperators
namespace Tensors
set_option linter.unusedVariables false in
axiom _root_.SoberonConvexBody.Tensors.IsONFrame.orthonormal : ∀ {q : Fin 4 → SoberonConvexBody.Tensors.E4},
  SoberonConvexBody.Tensors.IsONFrame q → Orthonormal ℝ q
/-- The given four vectors form an orthonormal basis, not merely a family. -/
def IsONFrame.toONBasis {q : Fin 4 -> E4} (hq : IsONFrame q) :
    OrthonormalBasis (Fin 4) Real E4 :=
  let b := basisOfOrthonormalOfCardEqFinrank hq.orthonormal (by simp [E4])
  b.toOrthonormalBasis (by
    simpa [b, coe_basisOfOrthonormalOfCardEqFinrank] using hq.orthonormal)

/-- Coordinates to ambient space. -/
def IsONFrame.toIsometry {q : Fin 4 -> E4} (hq : IsONFrame q) :
    E4 ≃ₗᵢ[Real] E4 := hq.toONBasis.repr.symm

end Tensors
end SoberonConvexBody

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.NearIdentity ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Elementary inverse estimates near the identity

The inverse is constructed by finite-dimensional injectivity. The second-order
estimate follows from the exact resolvent identity, not a matrix power series.
-/
noncomputable section
namespace SoberonConvexBody
open scoped BigOperators
open Tensors
namespace NearIdentity
def normalMap {q : Fin 4 -> E4} (hq : IsONFrame q) (n : Fin 4 -> E4) :
    E4 →ₗ[Real] E4 where
  toFun x := WithLp.toLp 2 (fun i => inner Real (hq.toIsometry x) (n i))
  map_add' x y := by
    ext i
    simp [inner_add_left]
  map_smul' a x := by
    ext i
    simp [real_inner_smul_left]

end NearIdentity
end SoberonConvexBody

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.Cells ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Sign cells and the finite Walsh criterion

This module separates the combinatorial meaning of the fifteen Walsh equations
from all geometry.  A boundary point is assigned to the positive side of each
oriented hyperplane, so the sixteen sign cells are literally disjoint and cover
all of space; no null-boundary hypothesis is needed for the partition itself.
-/
noncomputable section
namespace SoberonConvexBody
namespace Cells
open Set MeasureTheory
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
structure HyperplaneCfg where
  normal : Fin 4 → E4
  offset : Fin 4 → ℝ
end Cells
end SoberonConvexBody

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorLocal ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Local elimination of tensor zeros

This module proves local nonvanishing by exact polynomial elimination and
quadratic inequalities. No differentiability theorem or local inverse theorem
is needed. The neighborhood is a concrete open semialgebraic set of frames.
-/
noncomputable section
namespace SoberonConvexBody.Tensors
open Set
/-- Standard coordinate vector. -/
def coordinateVector (i : Fin 4) : E4 :=
  EuclideanSpace.single i 1

end SoberonConvexBody.Tensors

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.GeometryCore ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Geometric and measure-theoretic reduction

Unlike the earlier draft, this file does not package the analytic content in a
single certificate.  Every remaining analytic statement is exposed as a named
lemma with concrete definitions.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev HyperplaneCfg := Cells.HyperplaneCfg
end SoberonConvexBody

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.AffineBall ====
section
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Walsh integrals after straightening four affine hyperplanes

The affine map changes the body, not the signs. The transformed ball has the
explicit positive quadratic root developed in `EllipsoidExpansion`.
-/
noncomputable section
namespace SoberonConvexBody.Ellipsoid
open Set MeasureTheory
open scoped BigOperators
open Tensors  NearIdentity
def errorMatrix (e : E4 ≃ₗ[Real] E4) (i j : Fin 4) : Real :=
  e (coordinateVector j) i - if i=j then 1 else 0
end SoberonConvexBody.Ellipsoid

end
end

-- ==== Examples.akopjan__Grunbaum_counterexample.Examples.Example_fdf85e4943f0e5c1c864_BallLocal ====
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Simultaneous low and high coefficient estimates near an orthogonal frame

The Jacobian is the determinant of the explicitly constructed coordinate map.
The low coefficients detect offsets and pairwise scalar products; the high
coefficients have no terms of degree zero or one.
-/
noncomputable section
namespace SoberonConvexBody.BallLocal
open Set MeasureTheory
open scoped BigOperators
open Tensors  NearIdentity Ellipsoid


set_option linter.unusedVariables false in
theorem pair_gram_error (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : IsONFrame q)
    (e : E4 ≃ₗ[Real] E4) (he : forall x, e x = normalMap hq c.normal x)
    (d : Real) (hd : 0 ≤ d) (hn : forall i, norm (c.normal i-q i) ≤ d)
    (i j : Fin 4) (hij : i ≠ j) 
    (h_SoberonConvexBody_BallLocal_errorMatrix_normal : ∀ (c : SoberonConvexBody.HyperplaneCfg) (q : Fin 4 → SoberonConvexBody.E4)
      (hq : SoberonConvexBody.Tensors.IsONFrame q)
      (e : SoberonConvexBody.E4 ≃ₗ[ℝ] SoberonConvexBody.E4),
      (∀ (x : SoberonConvexBody.E4),
          (e : SoberonConvexBody.E4 → SoberonConvexBody.E4) x =
            (SoberonConvexBody.NearIdentity.normalMap hq c.normal :
                SoberonConvexBody.Tensors.E4 → SoberonConvexBody.Tensors.E4)
              x) →
        ∀ (i j : Fin 4),
          SoberonConvexBody.Ellipsoid.errorMatrix e i j =
            Inner.inner ℝ (c.normal i) (q j) - if i = j then 1 else 0)
    :
    |inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i)| ≤ d^2 := by
  have hid : inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i) =
      inner Real (c.normal i-q i) (c.normal j-q j) := by
    rw [h_SoberonConvexBody_BallLocal_errorMatrix_normal c q hq e he, h_SoberonConvexBody_BallLocal_errorMatrix_normal c q hq e he]
    simp only [if_neg hij,if_neg (Ne.symm hij),sub_zero,inner_sub_left,inner_sub_right,
      hq i j,if_neg hij,real_inner_comm (q i) (c.normal j)]
    ring
  rw [hid]
  calc
    |inner Real (c.normal i-q i) (c.normal j-q j)| ≤
        norm (c.normal i-q i)*norm (c.normal j-q j) := abs_real_inner_le_norm _ _
    _ ≤ d*d := mul_le_mul (hn i) (hn j) (norm_nonneg _) hd
    _ = d^2 := by ring
end SoberonConvexBody.BallLocal
