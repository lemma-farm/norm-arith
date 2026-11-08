-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Geometry.CubeMeasure
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Geometry.TriadicCubeTranslation
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open MeasureTheory
open scoped BigOperators ENNReal Topology
/-!
# Cube face reflections

This file begins the C.2 reflection infrastructure for the cube Neumann
`W^{2,2}` discharge.  The key analytic reflection step will be proved in weak
form; the lemmas here supply the affine one-coordinate face reflections and
their first coordinate-derivative chain rule.
-/
noncomputable section
end
end Homogenization
