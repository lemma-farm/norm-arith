-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.Mean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelBasic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelSegment
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelTime
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelPower
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.Smooth
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option warningAsError true
namespace CKN
/-!
# Finite-`p` convex-domain Poincare scaffolding

This wrapper module will be the stable import target for the future bounded
open convex domain `L^p` Poincare theorem family. For now it re-exports the
first two implementation layers:

- segment geometry and smooth FTC along affine segments;
- the mean-minus-average integral identity.

The eventual theorem surface should live here once the nested integral estimates
and the final convex-domain `L^p` bound are in place.
-/
end CKN
