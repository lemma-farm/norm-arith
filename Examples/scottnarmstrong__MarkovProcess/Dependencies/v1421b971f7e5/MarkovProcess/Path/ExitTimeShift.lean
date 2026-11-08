/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.ExitTime
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.Shift
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.ContinuousPath
section Shift
variable {alpha : Type*} [PseudoMetricSpace alpha]
end Shift
section Measurable
variable {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
end Measurable
end MarkovProcess.ContinuousPath
