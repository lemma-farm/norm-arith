-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open MeasureTheory
open scoped BigOperators ENNReal Topology
/-!
# Euclidean `L²` Calderon-Zygmund helpers

This file starts the `q = 2` Euclidean Calderon-Zygmund discharge.  The main
identity will be the smooth compactly supported integration-by-parts formula
`‖D²u‖₂ = ‖Δu‖₂`; the lemmas below package coordinate derivatives in the
project's `Vec d`/`basisVec` convention and record the support and symmetry
facts needed by the IBP chain.
-/
noncomputable section
end
end Homogenization
