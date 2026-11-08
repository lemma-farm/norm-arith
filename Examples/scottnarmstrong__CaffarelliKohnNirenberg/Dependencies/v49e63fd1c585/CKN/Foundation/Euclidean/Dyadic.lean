-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option warningAsError true
/-!
# Dyadic cubes in the native three-dimensional carrier

The cubes use the half-open product grid on `Vec3 = Fin 3 → ℝ`.  The scale
index is integral so that parent and child cubes are represented uniformly.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
abbrev DyadicCorner := Fin 3 → ℤ
structure DyadicIndex where
  scale : ℤ
  corner : DyadicCorner
def dyadicScale (k : ℤ) : ℝ := (2 : ℝ) ^ (-k : ℤ)
def dyadicCube (k : ℤ) (a : DyadicCorner) : Set Vec3 :=
  Set.univ.pi (fun i => Ico ((a i : ℝ) * dyadicScale k)
    (((a i : ℝ) + 1) * dyadicScale k))
def dyadicCubeCenter (k : ℤ) (a : DyadicCorner) : Vec3 :=
  fun i => ((a i : ℝ) + 1 / 2) * dyadicScale k
def dyadicParent (Q : DyadicIndex) : DyadicIndex :=
  { scale := Q.scale - 1
    corner := fun i => Q.corner i / 2 }
end CKN.Foundation.Euclidean
