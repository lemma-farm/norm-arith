module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.DensityPredicates
public import Mathlib
import all Mathlib.Order.Filter.ENNReal
@[expose] public section
/-!
# Numerical uniform Beurling densities

The normalized source profiles take their infimum or supremum over all
half-open real windows of a fixed positive length.  Their `liminf` and
`limsup` at real `atTop` are `ℝ≥0∞`-valued, so infinite upper density is
retained rather than truncated to a real number.
-/
namespace MeyerGeneralProblem
open Filter
noncomputable def upperUniformDensityProfile
    (S : LocallyFiniteCarrier) (L : ℝ) : ENNReal :=
  if 0 < L then
    ⨆ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L
  else 0
noncomputable def upperUniformBeurlingDensity
    (S : LocallyFiniteCarrier) : ENNReal :=
  Filter.limsup (upperUniformDensityProfile S) Filter.atTop
namespace LocallyFiniteCarrier
variable (S : LocallyFiniteCarrier)
theorem upperUniformDensityProfile_of_pos {L : ℝ} (hL : 0 < L) :
    upperUniformDensityProfile S L =
      ⨆ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L := by
  simp [upperUniformDensityProfile, hL]
end LocallyFiniteCarrier
end MeyerGeneralProblem
