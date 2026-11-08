-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Maximal.StrongType
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Morrey.Hedberg
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Morrey.Inclusions
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Morrey.Kernel
set_option autoImplicit false
set_option warningAsError true
/-!
# Hedberg and Adams estimates

This module connects the parabolic Riesz potential with the exported maximal
function estimates and the cylinder Morrey seminorm.
-/
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic.Morrey
