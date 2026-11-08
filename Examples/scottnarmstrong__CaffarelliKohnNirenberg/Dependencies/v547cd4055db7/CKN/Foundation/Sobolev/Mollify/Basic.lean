-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
set_option autoImplicit false
set_option warningAsError true
/-!
# ContDiffBump mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The custom convex-approximation chain was not used here: Mathlib
v4.34 already provides normalized `ContDiffBump` kernels, convolution
regularity, and approximate-identity convergence. This direct port keeps the
kernel and convolution API independent of the sibling geometry layer.
-/
open scoped Convolution Topology
namespace CKN
end CKN
