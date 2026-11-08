module
public import Mathlib
@[expose] public section
/-!
# Shared definitions

The definitions on which the compared statements rest. The block between the
`BEGIN`/`END SHARED DEFINITIONS` markers is copied byte for byte into `Challenge.lean`, so the
Challenge imports Mathlib only and elaborates the same declarations, under the same names, as the
proof modules, which are all built on this file.
-/
-- BEGIN SHARED DEFINITIONS
-- The definitions of this entry that the compared statements use. This block is, byte for byte,
-- the body of `InflationDimension/Defs.lean`, on which the proof modules are built; both files
-- import Mathlib only.
namespace InflationDimension
open Polynomial Filter Topology Module
open scoped Kronecker
noncomputable section
section Scheme
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The integer lattice `ℤ^ι ⊂ ℝ^ι`: the `ℤ`-span of the standard basis. -/
def intLattice (ι : Type*) [Fintype ι] [DecidableEq ι] : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
/-- The real-linear map `v ↦ A v` of an integer matrix `A` on `ℝ^ι`. -/
def act (A : Matrix ι ι ℤ) : Module.End ℝ (ι → ℝ) :=
  Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))
/-- An `A`-invariant cut-and-project scheme on the lattice `ℤ^ι`: a splitting `ℝ^ι = E ⊕ H`
into `A`-invariant subspaces (`E` physical, `H` internal) such that `ℤ^ι ∩ H = 0` (so the
projection to `E` along `H` is injective on the lattice) and the projection of `ℤ^ι` to `H`
along `E` is dense in `H`. Aperiodicity (`ℤ^ι ∩ E = 0`) is not required, and `H = 0` is
allowed. -/
structure InvariantCPS (A : Matrix ι ι ℤ) where
  /-- The physical space. -/
  E : Submodule ℝ (ι → ℝ)
  /-- The internal space. -/
  H : Submodule ℝ (ι → ℝ)
  isCompl : IsCompl E H
  mapsTo_E : ∀ v ∈ E, act A v ∈ E
  mapsTo_H : ∀ v ∈ H, act A v ∈ H
  inj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0
  dense : (H : Set (ι → ℝ)) ⊆ closure (H.projection E isCompl.symm '' (intLattice ι : Set (ι → ℝ)))
namespace InvariantCPS
variable {A : Matrix ι ι ℤ} (S : InvariantCPS A)
end InvariantCPS
end Scheme
section Spectrum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Spectrum
section JordanData
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end JordanData
section Instances
end Instances
end
end InflationDimension
-- END SHARED DEFINITIONS
