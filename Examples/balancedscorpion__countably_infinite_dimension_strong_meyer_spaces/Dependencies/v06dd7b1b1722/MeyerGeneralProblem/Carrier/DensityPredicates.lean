module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib
@[expose] public section
/-!
# Half-open window counts and strict uniform-density predicates

All source windows use the convention `[a, a + L)`.  The strict predicates
are deliberately stated using positive real window lengths, an explicit
positive density margin, and a positive eventual length threshold.  Numerical
`ℝ≥0∞` densities and their liminf/limsup equivalences belong in the subsequent
uniform-density layer.
-/
namespace MeyerGeneralProblem
/-- The number of carrier nodes in the half-open real window `[a, a + L)`. -/
noncomputable def windowCount (S : LocallyFiniteCarrier) (a L : ℝ) : ℕ :=
  Set.ncard (S.carrier ∩ Set.Ico a (a + L))
namespace LocallyFiniteCarrier
variable (S : LocallyFiniteCarrier)
end LocallyFiniteCarrier
/-- Uniform lower window growth strictly above `c`, in the exact half-open
source convention and with positive real window lengths. -/
def UniformLowerDensityGT (S : LocallyFiniteCarrier) (c : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → ∀ a : ℝ,
      (c + ε) * L ≤ (windowCount S a L : ℝ)
/-- Uniform upper window growth strictly below `c`, in the exact half-open
source convention and with positive real window lengths. -/
def UniformUpperDensityLT (S : LocallyFiniteCarrier) (c : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → ∀ a : ℝ,
      (windowCount S a L : ℝ) ≤ (c - ε) * L
namespace UniformLowerDensityGT
end UniformLowerDensityGT
namespace UniformUpperDensityLT
end UniformUpperDensityLT
namespace LocallyFiniteCarrier
variable (S : LocallyFiniteCarrier)
end LocallyFiniteCarrier
end MeyerGeneralProblem
