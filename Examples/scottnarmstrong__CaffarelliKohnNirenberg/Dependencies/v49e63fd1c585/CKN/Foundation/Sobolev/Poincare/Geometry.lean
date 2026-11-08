-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Ambient.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Measure.RestrictedVolume
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit false
set_option warningAsError true
/-!
# Geometry for ball Poincare estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  This file keeps the bounded convex-domain and affine-segment
interfaces needed by the ball estimate while using the established CKN carriers.
-/
namespace CKN
open MeasureTheory
/-- A coordinatewise bounded domain in the native finite-dimensional carrier. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U
namespace IsSobolevRegularDomain
end IsSobolevRegularDomain
/-- An open bounded convex domain in the native carrier. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U
namespace IsOpenBoundedConvexDomain
end IsOpenBoundedConvexDomain
end CKN
