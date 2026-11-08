module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib
@[expose] public section
/-!
# Indexed locally finite carriers

An `IndexedCarrier` carries a chosen countable, injective parametrisation.  It
is the coordinate-level companion of the extensional `LocallyFiniteCarrier`.
-/
namespace MeyerGeneralProblem
/-- A countably indexed, injective parametrisation with locally finite range. -/
structure IndexedCarrier (ι : Type*) [Countable ι] where
  /-- The physical carrier point at an index. -/
  point : ι → ℝ
  /-- Distinct indices give distinct physical nodes. -/
  injective : Function.Injective point
  /-- The range has finite intersection with every closed bounded interval. -/
  locallyFinite_range : ∀ a b : ℝ, (Set.range point ∩ Set.Icc a b).Finite
namespace IndexedCarrier
variable {ι : Type*} [Countable ι]
instance : FunLike (IndexedCarrier ι) ι ℝ where
  coe := IndexedCarrier.point
  coe_injective := by
    intro Λ Γ h
    cases Λ
    cases Γ
    simp_all
variable (Λ : IndexedCarrier ι)
end IndexedCarrier
namespace LocallyFiniteCarrier
end LocallyFiniteCarrier
namespace TwoSidedCarrier
end TwoSidedCarrier
end MeyerGeneralProblem
