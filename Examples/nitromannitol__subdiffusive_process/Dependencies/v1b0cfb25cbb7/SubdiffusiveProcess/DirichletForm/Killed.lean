/-
# Killed parts of a closed form on an open set
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.Regular
public import Mathlib
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
# Killed parts

The **part** of a closed form `E` on an open set `U` (the form "killed" outside
`U`) is the restriction of `E` to the closure, for the energy norm, of the core
functions supported in `U`.  This file axiomatizes that domain
(`SubdiffusiveProcess.DirichletForm.IsKilledDomain`), shows it is unique, and proves the two facts
the applications need:

* `SubdiffusiveProcess.DirichletForm.IsKilledDomain.le_of_subset`: consistency of killed parts,
  `q ⊆ U` implies `D(E^q) ⊆ D(E^U)`, with the forms agreeing;
* `SubdiffusiveProcess.DirichletForm.IsKilledDomain.eq_domain_of_isRegular`: for a regular form the
  killed domain on the whole space is the full domain.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §4.4 (parts of Dirichlet forms).
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-- `D` is the **killed domain** of `E` on `U`: it contains the core functions
supported in `U`, every element is an energy-norm limit of such functions, and
it is closed for the energy norm.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroIsKilledDomain`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure IsKilledDomain (E : ClosedForm m) (U : Set X) (D : Submodule ℝ (Lp ℝ 2 m)) :
    Prop where
  /-- The killed domain is contained in `D(E)`. -/
  le_domain : D ≤ E.domain
  /-- The killed domain contains every core function supported in `U`. -/
  memCoreOn_mem : ∀ u : Lp ℝ 2 m, E.MemCoreOn U u → u ∈ D
  /-- Every element of the killed domain is an energy-norm limit of core
  functions supported in `U`. -/
  approx : ∀ u ∈ D, ∀ ε : ℝ, 0 < ε →
    ∃ w : Lp ℝ 2 m, E.MemCoreOn U w ∧ E.energyNormSq (u - w) < ε
  /-- The killed domain is closed for the energy norm. -/
  isClosed : ∀ (u : ℕ → Lp ℝ 2 m) (w : Lp ℝ 2 m), (∀ n, u n ∈ D) → w ∈ E.domain →
    Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0) → w ∈ D
/-- `F` is the **killed part** of `E` on the open set `U`: its domain is the
killed domain and its form is the restriction of `E`.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroIsKilledPart`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure IsKilledPart (E : ClosedForm m) (U : Set X) (F : ClosedForm m) : Prop where
  /-- The domain of `F` is the killed domain of `E` on `U`. -/
  isKilledDomain : IsKilledDomain E U F.domain
  /-- `F` agrees with `E` on its domain. -/
  form_eq : ∀ u ∈ F.domain, ∀ v ∈ F.domain, F.form u v = E.form u v
namespace IsKilledDomain
variable {E : ClosedForm m}
end IsKilledDomain
end SubdiffusiveProcess.DirichletForm
