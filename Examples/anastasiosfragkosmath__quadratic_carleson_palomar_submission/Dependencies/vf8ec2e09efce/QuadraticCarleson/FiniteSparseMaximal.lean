/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Definitions
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite maxima of sparse operators

This file develops the sparse-family and finite-maximal ingredients of Lemma
`l:weak11sparse` in the paper.  In particular, it records measurability in the
definition of a sparse family, proves that a sparse family of nondegenerate
real intervals is countable, makes the infimum defining the sparse norm
usable, and verifies the two quantitative finite-dimensional steps in the
paper's proof: the Hölder estimate for the foliation by the linearizing index
and the logarithmic choice of exponents.
-/
open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace L0Infinity
end L0Infinity
structure RealInterval where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
/-- The interval itself.  Endpoint choices do not affect any later measure. -/
def RealInterval.carrier (I : RealInterval) : Set ℝ := Ioc I.left I.right
/-- Lebesgue length of an interval. -/
def RealInterval.length (I : RealInterval) : ℝ := I.right - I.left
theorem RealInterval.length_pos (I : RealInterval) : 0 < I.length := by
  exact sub_pos.mpr I.left_lt_right
def IsSparse (η : ℝ) (S : Set RealInterval) : Prop :=
  0 < η ∧ η < 1 ∧
    ∃ E : {I : RealInterval // I ∈ S} → Set ℝ,
      (∀ I, MeasurableSet (E I)) ∧
        (∀ I, E I ⊆ I.1.carrier) ∧
          (Pairwise fun I J ↦ Disjoint (E I) (E J)) ∧
            ∀ I, η * I.1.length ≤ (volume (E I)).toReal
/-- Every sparse collection of nondegenerate real intervals is countable.

This is what justifies the paper's unqualified sum over a sparse family.  The
proof uses the major subsets: they are measurable, pairwise disjoint, and
have strictly positive measure in the s-finite Lebesgue measure space. -/
theorem IsSparse.countable {η : ℝ} {S : Set RealInterval} (hS : IsSparse η S) :
    S.Countable := by
  rcases hS with ⟨hη, -, E, hEmeas, -, hEdisj, hEsize⟩
  have hEpos : ∀ I : {I : RealInterval // I ∈ S}, 0 < volume (E I) := by
    intro I
    have hreal : 0 < (volume (E I)).toReal :=
      lt_of_lt_of_le (mul_pos hη I.1.length_pos) (hEsize I)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hcount : Set.Countable
      {I : {I : RealInterval // I ∈ S} | 0 < volume (E I)} :=
    Measure.countable_meas_pos_of_disjoint_iUnion hEmeas hEdisj
  have huniv : {I : {I : RealInterval // I ∈ S} | 0 < volume (E I)} = Set.univ :=
    Set.eq_univ_of_forall hEpos
  rw [huniv, Set.countable_univ_iff] at hcount
  exact hcount
end QuadraticCarleson
