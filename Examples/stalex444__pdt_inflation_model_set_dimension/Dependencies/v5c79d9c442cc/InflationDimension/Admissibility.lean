module
public import Mathlib
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.Defs
@[expose] public section
/-!
# Admissibility of an invariant cut-and-project scheme, and Kronecker's density criterion

For an integer matrix `A` and an `A`-invariant cut-and-project scheme `ℝ^ι = E ⊕ H` on the
lattice `ℤ^ι`:

* `InvariantCPS.mapsTo_modelSet_iff`: `A Λ(W) ⊆ Λ(W)` if and only if `A` maps the lattice points
  `W ∩ π_H(ℤ^ι)` of the window into `W` (any `W`).
* `admissible_iff_powerBounded`: the scheme is admissible if and only if `A` is power-bounded on
  `H`; then the orbit window `W_*` is a compact, convex, centrally symmetric window with
  `A W_* ⊆ W_*` and `A Λ(W_*) ⊆ Λ(W_*)` (`InvariantCPS.orbitWindow_spec`).
* `roots_restrict_H_le_one`, `unstableCount_le_finrank`: on an admissible scheme every eigenvalue
  of `A|_H` lies in the closed unit disk, so the number `U(A)` of eigenvalues of modulus `> 1` is
  at most `dim E`.
* `kronecker_density_criterion`: the projection of `ℤ^ι` to `H` along `E` is dense in `H` if and
  only if every real functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero
  (Pleasants (2000), Cor. 2.12).

The two compared statements `admissibility_criterion` and `kronecker_density_criterion` are
proved at the end of the file. General facts about a finite-dimensional real space (the
characteristic polynomial of a direct sum, eigenvalues of a power-bounded map) are in the
namespace `InflationDimension.PowerBounded`; Kronecker's criterion for a `ℤ`-submodule `Γ`
spanning the space (`Γ + E` dense if and only if no nonzero functional is integral on `Γ` and
vanishes on `E`) is in `InflationDimension.KroneckerDensity`.
-/
namespace InflationDimension
open Polynomial Filter Topology Module
noncomputable section
/-! ### Linear algebra on a finite-dimensional real space -/
namespace PowerBounded
end PowerBounded
/-! ### Kronecker's density criterion in a finite-dimensional real space -/
namespace KroneckerDensity
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
end KroneckerDensity
open PowerBounded KroneckerDensity
/-! ### The lattice `ℤ^ι` and the action of `A` -/
section Lattice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace InvariantCPS
variable {A : Matrix ι ι ℤ} (S : InvariantCPS A)
end InvariantCPS
end Lattice
/-! ### The compared statements -/
end
end InflationDimension
