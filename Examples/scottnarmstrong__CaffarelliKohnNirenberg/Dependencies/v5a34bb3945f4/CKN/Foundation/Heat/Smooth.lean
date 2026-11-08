-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Heat.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit false
set_option warningAsError true
/-!
# Differentiation formulas for the heat kernel

The coordinate formulas below use the standard coordinate directions of
`Fin 3 → ℝ`.  They do not use the function space's ambient norm; all spatial
quadratic expressions are finite sums.
-/
open scoped BigOperators ENNReal Topology
open Filter Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
end CKN.Foundation.Heat
