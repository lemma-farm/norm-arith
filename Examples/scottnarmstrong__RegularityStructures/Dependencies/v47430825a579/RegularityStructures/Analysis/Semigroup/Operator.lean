/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Semigroup.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The operators `Q_t` of a regularising semigroup

Basic analysis of `K.apply t g (x) = ∫ Q_t(x, y) g(y) dy` on bounded measurable functions:

* `integrable_kernel`, `integral_abs_kernel_le`: `∫ |Q_t(x, y)| dy ≤ M₀` (the `r = 0` moment);
* `abs_apply_le`: `|Q_t g| ≤ M₀ ‖g‖_∞`;
* `measurable_apply`: `Q_t g` is measurable;
* `apply_apply`: `Q_s Q_t g = Q_{s+t} g` (Fubini and the semigroup property);
* `eq_of_abs_sub_le`: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C t^β`, `β > 0`, coincide.

Source: [Hos25] = arXiv:2310.07396v2, proof of Theorem 4.1.
-/
public section
open MeasureTheory Filter Set
open scoped Topology
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
end RegularityStructures.RegularisingSemigroup
end
