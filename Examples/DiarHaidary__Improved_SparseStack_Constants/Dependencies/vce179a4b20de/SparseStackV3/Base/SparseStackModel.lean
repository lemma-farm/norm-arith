/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/SparseStackModel.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.ParsevalFrame
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SparseFock
namespace SparseStackModel
open scoped BigOperators InnerProductSpace
open ParsevalFrame
noncomputable section
/-- A Rademacher sign, with no zero constructor. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq
/-- The exact real value of a Rademacher sign. -/
def Sign.val : Sign → ℝ
  | .plus => 1
  | .minus => -1
structure Sample (s b n : ℕ) where
  h : Fin s × Fin n → Fin b
  sign : Fin s × Fin n → Sign
def Sample.hash {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) : Fin b :=
  Z.h (g, i)
def Sample.sgn {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) : Sign :=
  Z.sign (g, i)
/-- The signed basis vector `X_{g i} = σ_{g i} e_{h_g(i)}`. -/
def signedBasis {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) :
    EVec b :=
  WithLp.toLp 2 fun a ↦ if a = Z.hash g i then (Z.sgn g i).val else 0
def invSqrt (s : ℕ) : ℝ := (Real.sqrt (s : ℝ))⁻¹
/-- The stacked sketch matrix, with rows indexed without flattening by
`Fin s × Fin b` and columns by `Fin n`. -/
def stackMatrix {s b n : ℕ} (Z : Sample s b n) :
    Matrix (Fin s × Fin b) (Fin n) ℝ :=
  fun r i ↦ invSqrt s * signedBasis Z r.1 i r.2
def sketchGram {s b n : ℕ} (Z : Sample s b n) : Matrix (Fin n) (Fin n) ℝ :=
  (stackMatrix Z).transpose * stackMatrix Z
def embeddedGram {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (rowMatrix F.u).transpose * (sketchGram Z * rowMatrix F.u)
/-- The Gram error `UᵀΠᵀΠU - I_d`. -/
def gramError {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  embeddedGram F Z - 1
end
end SparseStackModel
end SparseFock
