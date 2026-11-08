/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Mild
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.Interval.Set.Pi
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Mild solutions are differentiable in space

Let `G : ℝ × T³ × E → E` have a continuous derivative `DG` in `(x, u)` (on the periodic lift), let
`u₀ ∈ C(T³, E)` have a continuous derivative `Du₀`, and let `u` be a continuous mild solution of
`∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]`. Then every `u(t)`, `t ∈ [0, T]`, is
differentiable on the lift, and its derivative is a continuous path `w` in `C(T³, ℝ³ →L E)`.

The candidate `w` is the mild solution of the linearised equation
`∂_t w = Δw + D_x G(t, x, u) + D_u G(t, x, u) ∘ w`, `w(0) = Du₀`. For a fixed increment `k ∈ ℝ³`,
the error `e_k(t) = u(t, · + k) - u(t) - w(t) k` solves a linear mild equation whose forcing is a
first-order Taylor remainder of `G` and of `u₀`. A uniform Taylor estimate on a compact set and
Grönwall's inequality give `‖e_k(t)‖ = o(|k|)` uniformly in `t ∈ [0, T]`.
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]
end RegularityStructures.PDE
end
