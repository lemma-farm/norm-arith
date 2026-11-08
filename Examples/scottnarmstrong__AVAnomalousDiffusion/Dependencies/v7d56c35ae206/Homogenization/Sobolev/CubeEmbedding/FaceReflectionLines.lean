-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Sobolev.WeakDerivatives
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open Homogenization
open scoped BigOperators
/-!
# Single-face even reflection: definitions and per-line calculus

Global (on all of `ℝ^d`) even reflection of a function across the face
`{x_i = a}`, its candidate gradient (sign-flipped in direction `i` on the
reflected side), the geometric fact that the reflection commutes with coordinate
insertion, and the one-dimensional derivatives of the direct and reflected line
functions.  These feed the Fubini assembly in `FaceReflection`.
-/
noncomputable section
variable {d : ℕ}
end
end Homogenization
