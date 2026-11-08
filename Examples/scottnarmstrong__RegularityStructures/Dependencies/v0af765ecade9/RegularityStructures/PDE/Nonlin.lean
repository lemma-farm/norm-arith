/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v0af765ecade9.RegularityStructures.PDE.Mild
public import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Group.Quotient
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth nonlinearities and their jets

A nonlinearity `G : ℝ × T³ × F → F` is smooth when its lift
`nonlinLift G (s, y, v) = G(s, torusProj y, v)` is smooth on `ℝ × ℝ³ × F`. Its derivative in
`(x, u)` descends to a continuous map `nonlinDeriv G` on `ℝ × T³ × F`.

* `hasTorusDeriv_nemytskii`: the chain rule for `x ↦ G(s, x, v(x))`;
* `jetNonlin G`: the nonlinearity `(s, x, v, ω) ↦ (G(s, x, v), (D G(s, x, v)(eᵢ, ωᵢ))ᵢ)` of the
  system satisfied by a solution together with its first partial derivatives;
* `contDiff_nonlinLift_jetNonlin`: the jet nonlinearity of a smooth nonlinearity is smooth.
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
end RegularityStructures.PDE
end
public section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
public section
open Set Filter Topology
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
