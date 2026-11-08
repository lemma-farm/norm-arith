-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.G2.Algebra
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory Matrix
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)
end RothschildStein.G2
