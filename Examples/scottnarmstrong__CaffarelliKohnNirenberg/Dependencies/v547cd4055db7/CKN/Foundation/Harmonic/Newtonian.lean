-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Heat.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Heat.Convolution
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Heat.Smooth
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Heat.SpaceSecondDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# The Gaussian subordination identity for the Newtonian kernel

The time integral of the three-dimensional heat kernel is the Newtonian
kernel away from its singularity.  This identity is the scalar analytic
input for the heat-kernel route to the pressure decomposition.
-/
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
end CKN.Foundation.Heat
