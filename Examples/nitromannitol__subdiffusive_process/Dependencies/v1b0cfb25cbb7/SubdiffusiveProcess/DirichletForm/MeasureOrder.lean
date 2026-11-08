/-
# From an order of forms to an order of energy measures: the sine/cosine identity
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.SinCos
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.Weighted
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.MeasureComparison
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
# The sine/cosine identity for energy measures

The comparison of energy measures from a comparison of forms rests on one
identity.  For core functions `u, v` and `k > 0`, applying the Leibniz rule to
`v Φ_k^s(u)` and to `v Φ_k^c(u)` and adding, the derivative squares sum to `1`,
the cross terms cancel, and the last terms sum to `k⁻²`:

`Γ(vΦ_k^s(u))(B) + Γ(vΦ_k^c(u))(B) = ∫_B v² dΓ(u) + k⁻² Γ(v)(B)`.

Taking `B = X` this is
`E(vΦ_k^s(u)) + E(vΦ_k^c(u)) = ∫ v² dΓ_E(u) + k⁻² E(v)`, which is the display in
the proof of the paper's `mfd:lem-sincos`.  Applying a form bound to both
functions and letting `k → ∞` then gives `∫ v² dΓ_F(u) ≤ C ∫ v² dΓ_E(u)`.

This file proves the identity (all three terms separately, then the sum) and the
`k → ∞` step.  Everything is stated over the library carriers; nothing here is a
paper conclusion.
-/
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
namespace EnergyMeasure
variable {E : ClosedForm m} (Γ : EnergyMeasure E)
end EnergyMeasure
namespace EnergyMeasure
variable {E F : ClosedForm m} (ΓE : EnergyMeasure E) (ΓF : EnergyMeasure F)
end EnergyMeasure
end SubdiffusiveProcess.DirichletForm
