module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.TwoSided
public import Mathlib
import all Mathlib.Topology.DiscreteSubset
@[expose] public section
/-!
# Extensional locally finite carriers

This file provides the carrier interface used when no preferred enumeration is
part of the data.  Local finiteness is expressed on closed bounded intervals;
the resulting carrier is countable, closed, and discrete.
-/
namespace MeyerGeneralProblem
/-- A subset of the real line having finite intersection with every closed
bounded interval. -/
structure LocallyFiniteCarrier where
  /-- The underlying extensional carrier. -/
  carrier : Set ℝ
  /-- Every bounded closed interval contains only finitely many carrier points. -/
  finite_inter_Icc : ∀ a b : ℝ, (carrier ∩ Set.Icc a b).Finite
namespace LocallyFiniteCarrier
@[ext]
theorem ext {S T : LocallyFiniteCarrier} (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl
variable (S : LocallyFiniteCarrier)
/-- The type of points of an extensional carrier. -/
def subtype := S.carrier
theorem countable_carrier : S.carrier.Countable := by
  refine (Set.countable_iUnion fun n : ℕ ↦
    (S.finite_inter_Icc (-(n : ℝ)) n).countable).mono ?_
  intro x hx
  obtain ⟨n : ℕ, hn : |x| < n⟩ := exists_nat_gt |x|
  refine Set.mem_iUnion.mpr ⟨n, hx, ?_⟩
  exact ⟨(abs_lt.mp hn).1.le, (abs_lt.mp hn).2.le⟩
/-- The subtype of carrier points is countable. -/
instance countable_subtype : Countable S.subtype :=
  S.countable_carrier.to_subtype
end LocallyFiniteCarrier
namespace TwoSidedCarrier
end TwoSidedCarrier
end MeyerGeneralProblem
