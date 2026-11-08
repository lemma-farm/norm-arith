-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
set_option autoImplicit false
set_option warningAsError true
/-!
# Weak-derivative test functions

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port separates the bundled test-function facade from the
weak-derivative predicates and uses the `CKN` namespace.
-/
namespace CKN
/-- A smooth compactly supported test function supported inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U
instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun
end CKN
