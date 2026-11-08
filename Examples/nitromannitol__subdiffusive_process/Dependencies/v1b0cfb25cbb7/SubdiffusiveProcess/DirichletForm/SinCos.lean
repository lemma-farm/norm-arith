/-
# The rescaled sine and cosine used in the energy-measure order argument
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
# The rescaled sine and cosine

The comparison of energy measures from a comparison of forms uses the pair of
`C¹` functions `Φ_k^s(t) = k⁻¹ sin (k t)` and `Φ_k^c(t) = k⁻¹ cos (k t)`.  They
are bounded by `k⁻¹`, their derivatives have squares summing to `1`, and the
cross terms `Φ Φ'` of the two cancel, which is exactly what makes the Leibniz
rule collapse to `∫ v² dΓ(u) + k⁻² E(v)`.

This file records those identities.  They are pure real analysis and are stated
for their own sake; nothing here mentions a Dirichlet form.
-/
open Real
noncomputable section
namespace SubdiffusiveProcess.DirichletForm
end SubdiffusiveProcess.DirichletForm
