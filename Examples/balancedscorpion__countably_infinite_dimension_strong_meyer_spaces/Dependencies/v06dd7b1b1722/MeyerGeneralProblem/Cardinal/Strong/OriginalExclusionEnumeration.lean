module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Cardinal.Strong.NestedOriginalParameterLimit
public import Mathlib
@[expose] public section
/-! An ordinary complete enumeration of every accepted original equation code. -/
namespace MeyerGeneralProblem.StrongParity
/-- The ordinary encodable sum of the four original equation-data shapes. -/
abbrev OriginalExclusionCodeData :=
  (ℤ × ℚ × ℚ) ⊕ ((ℤ × ℤ × ℚ × ℚ) ⊕ ((ℤ × ℤ × ℚ × ℚ) ⊕ (ℤ × ℕ × ℕ)))
/-- Pack the actual integer/rational original equation data into an ordinary encodable type. -/
def ComputedRootExclusion.pack : ComputedRootExclusion → OriginalExclusionCodeData
  | .root n u v => .inl (n, u, v)
  | .difference n l u v => .inr (.inl (n, l, u, v))
  | .sum n l u v => .inr (.inr (.inl (n, l, u, v)))
  | .fixed n y gamma => .inr (.inr (.inr (n, y, gamma)))
/-- Unpack the ordinary data into the exact original equation code. -/
def unpackOriginalExclusion : OriginalExclusionCodeData → ComputedRootExclusion
  | .inl (n, u, v) => .root n u v
  | .inr (.inl (n, l, u, v)) => .difference n l u v
  | .inr (.inr (.inl (n, l, u, v))) => .sum n l u v
  | .inr (.inr (.inr (n, y, gamma))) => .fixed n y gamma
/-- Packing and unpacking preserve EVERY actual original equation code. -/
theorem unpackOriginalExclusion_pack (code : ComputedRootExclusion) :
    unpackOriginalExclusion code.pack = code := by cases code <;> rfl
/-- Actual ordinary encodability of all four original equation data shapes. -/
instance ComputedRootExclusion.encodable : Encodable ComputedRootExclusion :=
  Encodable.ofLeftInverse ComputedRootExclusion.pack unpackOriginalExclusion unpackOriginalExclusion_pack
noncomputable section
end
end MeyerGeneralProblem.StrongParity
