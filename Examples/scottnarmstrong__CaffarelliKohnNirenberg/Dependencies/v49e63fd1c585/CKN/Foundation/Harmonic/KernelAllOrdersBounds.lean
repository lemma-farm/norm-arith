-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersSmooth
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersOpen
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersSphere
import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# All-order derivative bounds for the Newtonian kernel

The Newtonian kernel `newtonianKernel` is homogeneous of degree `-1` and of
every finite differentiability order away from the origin, so its `k`-th
derivative is homogeneous of degree `-(1 + k)`.  Combining this with the
compactness of the Euclidean unit sphere gives, for each order `k`, a constant
`c` with

  `‖D^k newtonianKernel x‖ ≤ c ‖x‖₂^{-(1 + k)}`  for `x ≠ 0`,

and the same statement with exponent `-(2 + k)` for each first-order kernel
`∂_j newtonianKernel`.  These are the kernel estimates behind `cor:CZ-harmonic`
and the smoothness display `eq:har-Ck`.
-/
noncomputable section
namespace CKN.Foundation.Heat
end CKN.Foundation.Heat
