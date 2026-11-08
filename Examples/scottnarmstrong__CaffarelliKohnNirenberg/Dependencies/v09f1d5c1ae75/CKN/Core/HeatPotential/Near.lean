-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.HeatPotential.Morrey
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Heat.IntegralBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Parabolic.Morrey.AdamsBridge
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
/-!
The source block used for the local part of a heat potential.  The radius is
written with the gauge `parabolicRho₂`, whose time component is symmetric;
this is the geometry needed for a genuine parabolic metric ball.
-/
end CKN.Core.HeatPotential
