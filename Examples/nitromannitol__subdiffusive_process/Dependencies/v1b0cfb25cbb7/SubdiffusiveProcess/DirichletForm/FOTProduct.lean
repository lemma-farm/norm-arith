/-
# Lipschitz calculus and products on a Dirichlet form (Fukushima–Oshima–Takeda 1.4.1, 1.4.2)
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.Regular
public import Mathlib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Lipschitz calculus and products on a Dirichlet form

A `SubdiffusiveProcess.DirichletForm` only assumes that the unit contraction `t ↦ (t ∧ 1) ∨ 0` operates.  This file
derives from that single Markov clause and closedness the calculus of Fukushima–Oshima–Takeda
§1.4, with no regularity, locality or resolvent input:

* `SubdiffusiveProcess.DirichletForm.lipschitz_comp_mem`: if `G` is `L`-Lipschitz with `G 0 = 0` and `u ∈ D(E)`,
  then `G ∘ u ∈ D(E)` and `E(G ∘ u) ≤ L² E(u)` (Theorem 1.4.1 for `L = 1`;
  `SubdiffusiveProcess.DirichletForm.hasNormalContractions`).
* `SubdiffusiveProcess.DirichletForm.exists_mul_mem`: products of bounded elements of `D(E)` lie in `D(E)`
  (Theorem 1.4.2(ii)).
* `SubdiffusiveProcess.DirichletForm.exists_memCoreOn_mul_comp`, `SubdiffusiveProcess.DirichletForm.mul_comp_mem`,
  `SubdiffusiveProcess.DirichletForm.mul_mem`, `SubdiffusiveProcess.DirichletForm.comp_mem`, `SubdiffusiveProcess.DirichletForm.mul_mem_of_bounded`: the
  core `D(E) ∩ C_c` is stable under products and `C¹` functions (Theorem 1.4.2), in the exact
  shapes of the four closure clauses of `SubdiffusiveProcess.DirichletForm.IsCoreAlgebra`.

## Method

1. *Cross energies.*  If the ramp at level `h` returns `f` from `f + t g` for all `t > 0`,
   then `E(f, g) ≥ 0` (`form_nonneg_of_ramp_eq`).  Hence the slices of `u` over the cells
   `[i h, (i + 1) h]`, the reflected slices and the tail beyond `N h` have pairwise
   nonnegative cross energies.
2. *Piecewise-linear functions.*  A combination of these slices with coefficients of size at
   most `L` has energy at most `L² E(u)` (`sliceSum_mem_and_form_le`).
3. *Lower semicontinuity.*  A closed form is lower semicontinuous along `L²`-convergent
   sequences of bounded energy (`ClosedForm.mem_domain_of_tendsto_of_form_le`): the
   minimal-energy points of the convex hulls of the tails form an energy-Cauchy sequence by
   the parallelogram identity.
4. *Limit.*  The interpolants of `G` on finer and longer grids converge to `G ∘ u` in `L²` by
   dominated convergence (`tendsto_Lp_of_tendsto_comp`).
5. *Products* follow by polarization with a clamped square; *`C¹` functions* of bounded
   elements by clamping to the range, where they are Lipschitz.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  2nd edition, de Gruyter, 2011, Theorems 1.4.1 and 1.4.2.
-/
open MeasureTheory Filter Topology Set
open scoped NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-! ### Ramps -/
namespace ClosedForm
variable (E : ClosedForm m)
end ClosedForm
/-! ### Slices of the real line -/
section SliceReal
variable {h : ℝ} {i : ℕ} {s : ℝ}
end SliceReal
/-! ### Slices in `L²` -/
section Cross
variable (E : _root_.SubdiffusiveProcess.DirichletForm m) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {h : ℝ} (hh : 0 ≤ h)
include hu hh
end Cross
/-! ### Finite sums with nonnegative cross energies -/
namespace ClosedForm
variable (E : ClosedForm m)
end ClosedForm
/-! ### Energy of a weighted sum of slices -/
section Interp
variable {Γ : ℝ → ℝ} {L : ℝ≥0} {h : ℝ}
end Interp
/-! ### Convergence in `L²` of compositions -/
section Core
variable [TopologicalSpace X]
end Core
end SubdiffusiveProcess.DirichletForm
