-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Mollify.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersSphere
set_option autoImplicit false
set_option warningAsError true
namespace CKN
open Set MeasureTheory
open scoped Pointwise Convolution Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
/-!
# Support, mollifier support, and thickening lemmas

These five results were previously private lemmas in
`CKN/Foundation/Euclidean/RieszSecondExterior.lean` (the `d = 3` versions)
and `CKN/Foundation/Sobolev/Mollify/LpApproximation.lean` (the general `d`
version of `mollifier_tsupp_eq_closedBall`).  They are collected here as public
theorems.
-/
end CKN
