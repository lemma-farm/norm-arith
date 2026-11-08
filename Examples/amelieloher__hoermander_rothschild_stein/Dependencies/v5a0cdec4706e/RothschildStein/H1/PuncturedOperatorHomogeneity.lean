-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H1.DifferentialLocality
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H1.DifferentialScalar
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H1.SmoothGermExtension
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.G2.DilationMeasure
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
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)
end RothschildStein.H1
