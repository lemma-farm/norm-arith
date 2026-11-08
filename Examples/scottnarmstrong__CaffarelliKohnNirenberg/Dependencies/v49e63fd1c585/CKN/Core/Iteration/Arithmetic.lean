-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Setting.Monotonicity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Statements.Theta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# The arithmetic core of the scale iteration

This file records the real arithmetic used after the analytic decay estimate
in `paper/ckn.tex`, equations `eq:theta-decay-2` and `eq:kappa-props`.  The
analytic estimate itself is supplied as a hypothesis to the iteration theorem.
The radius interpolation theorem likewise takes the finiteness hypotheses
required by the radius monotonicity API.
-/
open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-! ### The numerical convention -/
end CKN
