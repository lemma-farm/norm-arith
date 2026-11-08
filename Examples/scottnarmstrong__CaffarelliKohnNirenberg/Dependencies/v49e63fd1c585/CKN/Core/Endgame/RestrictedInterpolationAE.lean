-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationRestricted
set_option autoImplicit false
set_option warningAsError true
/-! # Restricted interpolation with almost-everywhere sublinearity

This version of the restricted interpolation argument permits null exceptional
sets in sublinearity. The tail containment is interpreted modulo null sets;
the truncations, layer-cake argument, and numerical constant are unchanged
from `Foundation.Euclidean.InterpolationRestricted`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
end CKN.Core.Endgame
