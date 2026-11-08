-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v320eed9e9e4c.CKN.Foundation.Parabolic.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v320eed9e9e4c.CKN.Statements.SpaceTimeSet
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
set_option autoImplicit false
set_option warningAsError true
/-!
# Topology of parabolic space-time

The parabolic metric of `CKN.Foundation.Parabolic.Basic` is obtained by pulling back the
product metric of `L²(ℝ³) × ℝ` (the time factor being snowflaked) along `parabolicMap`.
This file identifies the resulting topology with the product topology of the spatial
variable and time.  It is the bridge that lets openness and closure of the paper's
space-time carriers be read off from the corresponding statements on `Vec3 × ℝ`: in
particular the space-time set `def:sws`, whose carrier is `Ω × I`, is open for open `Ω`
and `I`, and the interior and closure of a parabolic cylinder are computed from the
Euclidean ball and the intervals `Ioo` and `Icc`.
-/
open scoped Topology
open Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
end CKN.Foundation.Parabolic
