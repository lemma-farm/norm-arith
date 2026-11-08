module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.Indexed
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.SignedSquare
public import Mathlib
@[expose] public section
/-!
# Locally finite carriers in signed-square coordinates

The signed-square map is injective and proper on the real line.  Consequently
it sends every extensional locally finite carrier to another locally finite
carrier, without introducing multiplicity.
-/
namespace MeyerGeneralProblem
theorem mem_Icc_of_signedSquare_mem_Icc {x a b : ℝ}
    (hx : signedSquare x ∈ Set.Icc a b) :
    x ∈ Set.Icc (-(max |a| |b| + 1)) (max |a| |b| + 1) := by
  have hsquare : |x| ^ 2 ≤ max |a| |b| := by
    rw [← abs_signedSquare]
    exact abs_le_max_abs_abs hx.1 hx.2
  have hmax : 0 ≤ max |a| |b| :=
    le_trans (abs_nonneg a) (le_max_left _ _)
  have habs : |x| ≤ max |a| |b| + 1 := by
    by_contra hnot
    have hlarge : max |a| |b| + 1 < |x| := lt_of_not_ge hnot
    have hone : 1 ≤ |x| := by linarith
    have hmul : 0 ≤ |x| * (|x| - 1) :=
      mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hone)
    nlinarith
  exact (abs_le.mp habs)
/-- Signed-square images of locally finite carriers remain locally finite. -/
theorem LocallyFiniteCarrier.finite_signedSquare_image_inter_Icc
    (S : LocallyFiniteCarrier) (a b : ℝ) :
    (signedSquare '' S.carrier ∩ Set.Icc a b).Finite := by
  let R : ℝ := max |a| |b| + 1
  apply ((S.finite_inter_Icc (-R) R).image signedSquare).subset
  rintro y ⟨⟨x, hxS, rfl⟩, hxIcc⟩
  exact ⟨x, ⟨hxS, mem_Icc_of_signedSquare_mem_Icc hxIcc⟩, rfl⟩
namespace LocallyFiniteCarrier
/-- The extensional signed-square image of a locally finite carrier. -/
def signedSquareImage (S : LocallyFiniteCarrier) : LocallyFiniteCarrier where
  carrier := signedSquare '' S.carrier
  finite_inter_Icc := S.finite_signedSquare_image_inter_Icc
@[simp]
theorem signedSquareImage_carrier (S : LocallyFiniteCarrier) :
    S.signedSquareImage.carrier = signedSquare '' S.carrier := rfl
end LocallyFiniteCarrier
namespace TwoSidedCarrier
end TwoSidedCarrier
end MeyerGeneralProblem
