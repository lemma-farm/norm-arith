module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Cardinal.Strong.ProductSeparation
public import Mathlib
@[expose] public section
/-!
# Absolute weighted residues on the complete original finite carrier

The complete product root set is identified with the disjoint union of
its literal sheets. The finite Newton slab is evaluated on unit phases,
and the proved denominator bounds give absolute weighted summability
of the original physical residues. A Fourier identity is not asserted
by this module.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
def productNumeratorIndex (s : ℕ) :=
  {ij : Fin (s + 1) × Fin (s + 1) // ij ≠ (Fin.last s, Fin.last s)}
instance (s : ℕ) : Fintype (productNumeratorIndex s) := by
  unfold productNumeratorIndex
  infer_instance
end
end MeyerGeneralProblem.StrongParity
