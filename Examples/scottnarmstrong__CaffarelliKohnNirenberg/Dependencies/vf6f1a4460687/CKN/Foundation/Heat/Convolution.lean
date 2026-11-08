-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Heat.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Heat.Bounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Sobolev.Ambient.Basis
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Pressure.LeibnizLaplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction
set_option autoImplicit false
set_option warningAsError true
/-!
# Heat-kernel convolution

This file records the scalar convolution interface used by the heat-kernel
route to the Newtonian kernel.  The heat kernel is the left factor and the
compactly supported function is the right factor, so Mathlib's right-factor
regularity and derivative-transport theorems apply directly.
-/
open scoped Convolution
open scoped BigOperators
open scoped Topology
open MeasureTheory MeasureTheory.Measure
open Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
end CKN.Foundation.Heat
