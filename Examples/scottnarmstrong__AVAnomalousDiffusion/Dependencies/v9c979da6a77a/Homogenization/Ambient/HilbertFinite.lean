-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Ambient.BlockMatrix
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
/-!
This file provides finite-dimensional Hilbert realizations of `\R^d` and
`\R^{2d}` that stay compatible with the project's anti-`EuclideanSpace`
architecture.

The ambient algebraic carriers remain

- `Vec d = Fin d → ℝ`,
- `BlockVec d = Vec d × Vec d`.

Those are excellent lightweight types for most of the development, but their
default normed-space instances are not the Euclidean `L²` ones needed for the
Hilbert-space part of the coarse-graining theory. For that role we introduce
separate wrappers built from `PiLp 2`.
-/
/-- The Euclidean Hilbert realization of `\R^d`, presented without exposing
`EuclideanSpace` in the public API. -/
abbrev HilbertVec (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)
namespace HilbertVec
abbrev toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  fun i => x i
@[ext] theorem ext {d : ℕ} {x y : HilbertVec d} (h : ∀ i, x i = y i) : x = y :=
  PiLp.ext h
@[simp] theorem inner_def {d : ℕ} (x y : HilbertVec d) :
    inner ℝ x y = vecDot x.toVec y.toVec := by
  rw [PiLp.inner_apply, vecDot]
  simp_rw [RCLike.inner_apply]
  congr with i
  simp [toVec, mul_comm]
end HilbertVec
/-- The Euclidean Hilbert realization of `d × d` real matrices. The algebraic
carrier `Mat d` keeps its lightweight pointwise role; this wrapper is for
Hilbert-space measurability and `L²` arguments. -/
abbrev HilbertMat (d : ℕ) := PiLp 2 (fun _ : Fin d => HilbertVec d)
namespace HilbertMat
@[ext] theorem ext {d : ℕ} {A B : HilbertMat d} (h : ∀ i j, A i j = B i j) :
    A = B := by
  apply PiLp.ext
  intro i
  apply HilbertVec.ext
  intro j
  exact h i j
@[simp] theorem inner_def {d : ℕ} (A B : HilbertMat d) :
    inner ℝ A B = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp [HilbertVec.inner_def, vecDot]
end HilbertMat
/-- The Euclidean Hilbert realization of `\R^{2d}`, viewed as a doubled
potential/flux carrier. -/
abbrev HilbertBlockVec (d : ℕ) := PiLp 2 (fun _ : Fin 2 => HilbertVec d)
namespace HilbertBlockVec
/-- The potential component of a doubled Hilbert vector. -/
abbrev potential {d : ℕ} (X : HilbertBlockVec d) : HilbertVec d :=
  X 0
/-- The flux component of a doubled Hilbert vector. -/
abbrev flux {d : ℕ} (X : HilbertBlockVec d) : HilbertVec d :=
  X 1
abbrev toBlockVec {d : ℕ} (X : HilbertBlockVec d) : BlockVec d :=
  (X.potential.toVec, X.flux.toVec)
@[ext] theorem ext {d : ℕ} {X Y : HilbertBlockVec d}
    (hpot : X.potential = Y.potential) (hflux : X.flux = Y.flux) : X = Y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa [potential] using hpot
  · simpa [flux] using hflux
@[simp] theorem inner_def {d : ℕ} (X Y : HilbertBlockVec d) :
    inner ℝ X Y = blockVecDot X.toBlockVec Y.toBlockVec := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [blockVecDot, HilbertVec.inner_def]
end HilbertBlockVec
end Homogenization
