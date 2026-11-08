/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant
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
# Closed symmetric forms and Dirichlet forms

Let `m` be a measure on a measurable space `X`.  A **closed form** on `L²(X, m)`
is a densely defined, symmetric, nonnegative bilinear form `E` whose domain
`D(E)` is a submodule of `L²(X, m)` complete for the energy norm
`E₁(u) = E(u, u) + ‖u‖²`.  A **Dirichlet form** is a closed form on which the
unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm m`: a densely defined, symmetric, nonnegative,
  closed bilinear form on `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.energyInner`, `SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq`:
  the energy inner product `E₁(u, v) = E(u, v) + ⟪u, v⟫` and `E₁(u) = E₁(u, u)`.
* `SubdiffusiveProcess.DirichletForm.IsNormalContraction`: `T : ℝ → ℝ` with `T 0 = 0` and
  `|T s - T t| ≤ |s - t|`.
* `SubdiffusiveProcess.DirichletForm.unitTruncation`: the unit contraction `t ↦ (t ⊓ 1) ⊔ 0`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.OperatesOn`: `T` operates on `E`, i.e. `T ∘ u` stays
  in `D(E)` and does not increase the energy.
* `SubdiffusiveProcess.DirichletForm`: a closed form on which `unitTruncation` operates.
* `SubdiffusiveProcess.DirichletForm.HasNormalContractions`: the Fukushima–Oshima–Takeda statement
  that *every* normal contraction operates on a Dirichlet form.

## Implementation notes

The bilinear form is carried as a total function `Lp ℝ 2 m → Lp ℝ 2 m → ℝ`; every
axiom is restricted to the domain, so the values off the domain carry no
information.  This keeps statements free of subtype coercions and matches the
way a form defined by a dual (resolvent) expression is met in practice.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, de Gruyter, 2011.
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
namespace SubdiffusiveProcess.DirichletForm
/-- The unit contraction `t ↦ (t ⊓ 1) ⊔ 0` of the real line. -/
def unitTruncation (t : ℝ) : ℝ := max (min t 1) 0
structure ClosedForm (m : Measure X) where
  /-- The form domain `D(E)`, a linear subspace of `L²(X, m)`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The bilinear form `E(u, v)`.  Values outside `domain` carry no
  information: every axiom below is restricted to `domain`. -/
  form : Lp ℝ 2 m → Lp ℝ 2 m → ℝ
  /-- `D(E)` is dense in `L²(X, m)`. -/
  denseDomain : Dense (domain : Set (Lp ℝ 2 m))
  /-- `E(u, v) = E(v, u)`. -/
  form_symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- `E` is additive in its first argument. -/
  form_add_left : ∀ u ∈ domain, ∀ v ∈ domain, ∀ w ∈ domain,
    form (u + v) w = form u w + form v w
  /-- `E` is homogeneous in its first argument. -/
  form_smul_left : ∀ c : ℝ, ∀ u ∈ domain, ∀ v ∈ domain, form (c • u) v = c * form u v
  /-- `E(u, u) ≥ 0`. -/
  form_nonneg : ∀ u ∈ domain, 0 ≤ form u u
  /-- `E` is closed: `D(E)` is complete for the energy norm
  `E₁(u) = E(u, u) + ‖u‖²`. -/
  complete : ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ domain) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) →
    ∃ w ∈ domain, Tendsto
      (fun n => form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0)
namespace ClosedForm
variable {m : Measure X} (E : ClosedForm m)
theorem form_add_right {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : E.form u (v + w) = E.form u v + E.form u w := by
  rw [E.form_symm u hu _ (E.domain.add_mem hv hw), E.form_add_left v hv w hw u hu,
    E.form_symm v hv u hu, E.form_symm w hw u hu]
/-- `E` is homogeneous in its second argument. -/
theorem form_smul_right (c : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) : E.form u (c • v) = c * E.form u v := by
  rw [E.form_symm u hu _ (E.domain.smul_mem c hv), E.form_smul_left c v hv u hu,
    E.form_symm v hv u hu]
/-- `E(-u, v) = -E(u, v)`. -/
theorem form_neg_left {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (-u) v = -E.form u v := by
  simpa using E.form_smul_left (-1) u hu v hv
theorem form_sub_left {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : E.form (u - v) w = E.form u w - E.form v w := by
  rw [sub_eq_add_neg, E.form_add_left u hu _ (E.domain.neg_mem hv) w hw,
    E.form_neg_left hv hw, sub_eq_add_neg]
theorem form_add_self {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) = E.form u u + 2 * E.form u v + E.form v v := by
  rw [E.form_add_left u hu v hv _ (E.domain.add_mem hu hv), E.form_add_right hu hu hv,
    E.form_add_right hv hu hv, E.form_symm v hv u hu]
  ring
/-- Expansion of `E(u + t • v, u + t • v)`. -/
theorem form_add_smul_self (t : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) :
    E.form (u + t • v) (u + t • v) =
      E.form u u + 2 * t * E.form u v + t ^ 2 * E.form v v := by
  rw [E.form_add_self hu (E.domain.smul_mem t hv), E.form_smul_right t hu hv,
    E.form_smul_left t v hv _ (E.domain.smul_mem t hv), E.form_smul_right t hv hv]
  ring
/-- The Cauchy–Schwarz inequality for a nonnegative symmetric form, in squared
form. -/
theorem form_sq_le_mul {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u v ^ 2 ≤ E.form u u * E.form v v := by
  have key : ∀ t : ℝ, 0 ≤ E.form v v * (t * t) + 2 * E.form u v * t + E.form u u := by
    intro t
    have h := E.form_nonneg _ (E.domain.add_mem hu (E.domain.smul_mem t hv))
    rw [E.form_add_smul_self t hu hv] at h
    nlinarith [h]
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith [h]
/-- The Cauchy–Schwarz inequality for a nonnegative symmetric form. -/
theorem abs_form_le {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    |E.form u v| ≤ Real.sqrt (E.form u u) * Real.sqrt (E.form v v) := by
  have h := E.form_sq_le_mul hu hv
  rw [← Real.sqrt_mul_self (abs_nonneg (E.form u v)), ← Real.sqrt_mul (E.form_nonneg u hu)]
  refine Real.sqrt_le_sqrt ?_
  rw [abs_mul_abs_self, ← sq]
  exact h
def energyNormSq (u : Lp ℝ 2 m) : ℝ := E.form u u + ‖u‖ ^ 2
theorem form_le_energyNormSq {u : Lp ℝ 2 m} : E.form u u ≤ E.energyNormSq u := by
  simp only [energyNormSq]
  nlinarith [sq_nonneg ‖u‖]
end ClosedForm
end SubdiffusiveProcess.DirichletForm
/-- A **Dirichlet form** on `L²(X, m)`: a closed symmetric nonnegative form on
which the unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroDirichletForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure SubdiffusiveProcess.DirichletForm (m : Measure X) extends _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m where
  /-- The Markov property: the unit contraction operates on `E`. -/
  markov : ∀ u ∈ domain, ∀ v : Lp ℝ 2 m,
    (⇑v =ᵐ[m] fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x)) →
    v ∈ domain ∧ form v v ≤ form u u
namespace SubdiffusiveProcess.DirichletForm
variable {m : Measure X}
end SubdiffusiveProcess.DirichletForm
