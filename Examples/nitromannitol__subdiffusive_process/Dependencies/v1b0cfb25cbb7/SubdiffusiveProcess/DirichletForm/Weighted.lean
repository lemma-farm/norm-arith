/-
# Weighted forms `E^w(u, v) = ∫ w dΓ(u, v)`
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.EnergyMeasure
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
# Weighted forms

Given a closed form `E` with energy measure `Γ` and a weight `w : X → ℝ`, the
**weighted form** `E^w` is characterized by `E^w(u, v) = ∫ w dΓ(u, v)`.  This
file records that characterization (`SubdiffusiveProcess.DirichletForm.IsWeightedForm`) and derives
the two-sided comparison `(inf w) E ≤ E^w ≤ (sup w) E` from it.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §3.2 (the energy-measure calculus used to build weighted forms).
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-- `F` is the `w`-weighted form of `E`: it has the same domain and
`F(u, v) = ∫ w dΓ(u, v)`.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroIsWeightedForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure IsWeightedForm (E F : ClosedForm m) (Γ : EnergyMeasure E) (w : X → ℝ) :
    Prop where
  /-- `D(E^w) = D(E)`. -/
  domain_eq : F.domain = E.domain
  /-- `E^w(u) = ∫ w dΓ(u)`. -/
  energy_eq : ∀ u ∈ E.domain, F.form u u = ∫ x, w x ∂(Γ.measure u)
  /-- `E^w(u, v) = ∫ w dΓ(u, v)`. -/
  form_eq : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    F.form u v = signedIntegralOn (Γ.cross u v) Set.univ w
namespace IsWeightedForm
variable {E F : ClosedForm m} {Γ : EnergyMeasure E} {w : X → ℝ}
end IsWeightedForm
section Bounded
variable [OpensMeasurableSpace X]
end Bounded
end SubdiffusiveProcess.DirichletForm
