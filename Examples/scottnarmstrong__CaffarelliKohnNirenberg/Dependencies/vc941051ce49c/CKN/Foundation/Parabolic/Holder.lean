-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α
namespace ParabolicHolderSeminormLE
theorem mono_set {U V : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {α K : ℝ} (h : ParabolicHolderSeminormLE U g α K) (hVU : V ⊆ U) :
    ParabolicHolderSeminormLE V g α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)
end ParabolicHolderSeminormLE
end CKN.Foundation.Parabolic
