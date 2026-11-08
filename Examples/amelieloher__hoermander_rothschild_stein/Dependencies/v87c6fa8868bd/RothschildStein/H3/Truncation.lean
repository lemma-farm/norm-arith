-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.G2.GaugeConsequences
public import Mathlib.Topology.MetricSpace.Lipschitz
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open RothschildStein.G2
/-- The fixed radial cutoff (BB Lemma 8.24, pp. 354–356). -/
def radialCutoff (t : ℝ) : ℝ := min 1 (max 0 (2 - t))
/-- The cutoff takes values in the unit interval. -/
theorem radialCutoff_bounds (t : ℝ) : 0 ≤ radialCutoff t ∧ radialCutoff t ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _
end RothschildStein.H3
