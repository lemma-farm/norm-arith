-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option warningAsError true
/-! # Tensor-indexed pressure estimates

The pressure is identified with the sum of nine separately indexed operator
outputs. Component estimates then give an extended-valued norm bound and the
real pressure norm bound. Compact support is not needed for this consumption
step once the component estimates are supplied.
-/
open MeasureTheory
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
end CKN.Core.Endgame
