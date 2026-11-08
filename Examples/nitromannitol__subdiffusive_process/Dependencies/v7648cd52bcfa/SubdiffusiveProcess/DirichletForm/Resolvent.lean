/-
# Resolvents and the dual (variational) form of the energy
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.Energy
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
# Resolvents and the dual energy

A closed form `E` determines, for `α > 0`, the resolvent `G_α = (α + A)⁻¹` of its
associated nonnegative self-adjoint operator `A`, characterized by
`α⟪G_α f, v⟫ + E(G_α f, v) = ⟪f, v⟫` for all `v ∈ D(E)`
(`SubdiffusiveProcess.DirichletForm.IsResolvent`).  Conversely the energy is recovered from the
resolvent by the variational (dual) formula

`E_α(u) = sup_f (2⟪f, u⟫ - ⟪f, G_α f⟫)`,

which is `SubdiffusiveProcess.DirichletForm.dualEnergy`.  This file fixes both notions and proves
the elementary facts that do not need the spectral theorem: a resolvent is
symmetric and positive, and the dual energy is nonnegative and is `⊤` exactly
off its domain.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §1.3–§1.4.
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-- `G` is the resolvent of `E` at `α`: `G f ∈ D(E)` and
`α⟪G f, v⟫ + E(G f, v) = ⟪f, v⟫` for every `v ∈ D(E)`. -/
def IsResolvent (E : ClosedForm m) (α : ℝ) (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Prop :=
  ∀ f : Lp ℝ 2 m, G f ∈ E.domain ∧
    ∀ v ∈ E.domain, α * (inner ℝ (G f) v : ℝ) + E.form (G f) v = (inner ℝ f v : ℝ)
namespace IsResolvent
variable {E : ClosedForm m} {α : ℝ} {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
theorem mem_domain (h : IsResolvent E α G) (f : Lp ℝ 2 m) : G f ∈ E.domain := (h f).1
end IsResolvent
end SubdiffusiveProcess.DirichletForm
