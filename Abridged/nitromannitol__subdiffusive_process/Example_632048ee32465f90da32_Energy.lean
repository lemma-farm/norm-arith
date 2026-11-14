module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.vb9fcc8382cc5.SubdiffusiveProcess.DirichletForm.Basic ====
public section
/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
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

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.form_sub_left.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v w : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → v ∈ E.domain → w ∈ E.domain → E.form (u - v) w = E.form u w - E.form v w

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.abs_form_le.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → v ∈ E.domain → |E.form u v| ≤ √(E.form u u) * √(E.form v v)
def energyNormSq (u : Lp ℝ 2 m) : ℝ := E.form u u + ‖u‖ ^ 2
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.form_le_energyNormSq.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u : ↥(MeasureTheory.Lp ℝ 2 m)},
  E.form u u ≤ E.energyNormSq u
end ClosedForm
end SubdiffusiveProcess.DirichletForm

namespace SubdiffusiveProcess.DirichletForm
variable {m : Measure X}
end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_632048ee32465f90da32_Energy ====
/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
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
# Extended energy, order of forms, Mosco convergence

For a closed form `E` we extend `u ↦ E(u, u)` to all of `L²(X, m)` by `⊤`
outside the domain (`SubdiffusiveProcess.DirichletForm.ClosedForm.energy`).  This makes the domain
readable off the functional and lets the order of forms and Mosco convergence be
stated without side conditions.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm.energy`: `E(u) ∈ EReal`, equal to `⊤` off `D(E)`.
* the `Preorder` on `ClosedForm m` given by `E ≤ F ↔ ∀ u, E(u) ≤ F(u)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.LEWithConst`: `E ≤ C · F` on `D(F)`.
* `SubdiffusiveProcess.DirichletForm.TendstoWeakly`: weak convergence in `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.MoscoConverges`: Mosco convergence (weak liminf bound and
  existence of a strong recovery sequence).

## References

* U. Mosco, *Composite media and asymptotic Dirichlet forms*, J. Funct. Anal.
  123 (1994).
-/
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
namespace ClosedForm
variable (E F : ClosedForm m)


theorem tendsto_form_of_tendsto_energyNormSq {E : ClosedForm m} {u : ℕ → Lp ℝ 2 m}
    {w v : Lp ℝ 2 m} (hu : ∀ n : ℕ, u n ∈ E.domain) (hw : w ∈ E.domain)
    (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0)) :
    Tendsto (fun n => E.form (u n) v) atTop (𝓝 (E.form w v)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ n : ℕ, dist (E.form (u n) v) (E.form w v) ≤
      Real.sqrt (E.energyNormSq (u n - w)) * Real.sqrt (E.form v v) := by
    intro n
    rw [Real.dist_eq, ← E.form_sub_left (hu n) hw hv]
    refine (E.abs_form_le (E.domain.sub_mem (hu n) hw) hv).trans ?_
    have := E.form_le_energyNormSq (u := u n - w)
    have hnn := E.form_nonneg _ (E.domain.sub_mem (hu n) hw)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt this) (Real.sqrt_nonneg _)
  refine squeeze_zero (fun n => dist_nonneg) hb ?_
  have hs : Tendsto (fun n : ℕ => Real.sqrt (E.energyNormSq (u n - w))) atTop (𝓝 0) := by
    simpa using! (Real.continuous_sqrt.tendsto 0).comp h
  simpa using hs.mul_const (Real.sqrt (E.form v v))
end ClosedForm
end SubdiffusiveProcess.DirichletForm
