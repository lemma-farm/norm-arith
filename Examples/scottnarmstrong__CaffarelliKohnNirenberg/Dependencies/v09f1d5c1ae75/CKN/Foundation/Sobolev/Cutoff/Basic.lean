-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Support
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative smooth cutoff data

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the cutoff bundle and the explicit Euclidean
gradient API in the independent `CKN` namespace.

## Main definitions

* `CKN.vecEuclideanNorm`: the Euclidean norm on native coordinate vectors.
* `CKN.classicalGradient`: the coordinate gradient of a scalar function.
* `CKN.QuantitativeSmoothCutoff`: quantitative smooth cutoff data.

## Main results

* `QuantitativeSmoothCutoff.sq`: squaring a cutoff doubles its gradient bound.
* `QuantitativeSmoothCutoff.sq_toFun` and `QuantitativeSmoothCutoff.sq_apply`:
  the square operation has the expected pointwise form.
* `QuantitativeSmoothCutoff.mem_Icc`: every cutoff value lies in `[0, 1]`.
-/
open scoped BigOperators
namespace CKN
/-- The Euclidean dot product on native coordinate vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native coordinate vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x
/-- The Euclidean norm on native coordinate vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)
structure QuantitativeSmoothCutoff {d : ℕ}
    (inner outer : Set (Vec d)) (K : ℝ) where
  /-- The cutoff function. -/
  toFun : Vec d → ℝ
  /-- Smoothness to every order. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- The cutoff has compact topological support. -/
  hasCompactSupport : HasCompactSupport toFun
  /-- The topological support lies in the prescribed outer set. -/
  tsupport_subset : tsupport toFun ⊆ outer
  /-- The cutoff is nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The cutoff is at most one. -/
  le_one : ∀ x, toFun x ≤ 1
  /-- The cutoff equals one throughout the inner set. -/
  eq_one_on_inner : ∀ x ∈ inner, toFun x = 1
  /-- Pointwise explicit Euclidean gradient bound. -/
  gradient_bound :
    ∀ x, vecEuclideanNorm (classicalGradient toFun x) ≤ K
namespace QuantitativeSmoothCutoff
variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}
instance :
    CoeFun (QuantitativeSmoothCutoff inner outer K)
      (fun _ => Vec d → ℝ) where
  coe η := η.toFun
end QuantitativeSmoothCutoff
end CKN
