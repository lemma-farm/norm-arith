-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.HessianL2
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.CZDecomposition
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.CZDecompositionExistence
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.Hormander
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
def rieszSecondCubeStar (Q : DyadicIndex) : Set Vec3 :=
  {x | vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner) ≤
    2 * Real.sqrt 3 * (dyadicScale Q.scale / 2)}
end CKN.Foundation.Euclidean
